use grandiose_stage0::{
    BOOTSTRAP_MANIFEST_MAGIC, BOOTSTRAP_MANIFEST_SCHEMA, BootstrapArtifactCompatibilityError,
    BootstrapConvergenceError, BootstrapLimits, BootstrapManifest, BootstrapManifestError,
    BootstrapStage, Budget, CancellationToken, CompilationMode, CompilationRequest,
    CompileDiagnostic, CompilerBuildIdentity, DependencyNode, DependencyStatus, DiagnosticClass,
    Digest, FileKey, HostImportSelector, InstanceLimits, LogicalPath, ModuleKey, PackageKey,
    PackageSessionStatus, PrimitiveRole, PrimitiveSelector, RetentionReport, RuntimeManifestInput,
    Severity, SourceInput, StageZeroCompiler, VmArtifactError, VmContinuationPolicy,
    VmExecutionLimits, VmGenericArgument, VmInstruction, VmType, decode_and_verify_program,
    decode_program, encode_program,
    query::{Query, QueryCompleteness, QueryContext, QueryEngine, QueryFailure, QueryValue},
};
use std::{collections::BTreeMap, sync::Arc};

fn request(source: &str) -> CompilationRequest {
    CompilationRequest {
        build: CompilerBuildIdentity {
            compiler: Digest::of_bytes(b"service"),
            language_generation: 1,
            query_generation: 1,
            interface_generation: 1,
            cache_generation: 1,
            bytecode_generation: 1,
            verifier_generation: 1,
        },
        mode: CompilationMode::Build,
        root_package: PackageKey("app@0.1.0".into()),
        sources: vec![SourceInput::new(
            PackageKey("app@0.1.0".into()),
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

fn request_with_module(root: &str, child: &str) -> CompilationRequest {
    let package = PackageKey("app@0.1.0".into());
    let mut request = request(root);
    request.sources.push(SourceInput::new(
        package,
        LogicalPath::parse("src/math/math.glorious").unwrap(),
        child.as_bytes(),
    ));
    request
}

fn request_with_modules(root: &str, modules: &[(&str, &str)]) -> CompilationRequest {
    let package = PackageKey("app@0.1.0".into());
    let mut request = request(root);
    for (name, source) in modules {
        request.sources.push(SourceInput::new(
            package.clone(),
            LogicalPath::parse(format!("src/{name}/{name}.glorious")).unwrap(),
            source.as_bytes(),
        ));
    }
    request
}

fn request_with_logical_sources(root: &str, sources: &[(&str, &str)]) -> CompilationRequest {
    let package = PackageKey("app@0.1.0".into());
    let mut request = request(root);
    for (path, source) in sources {
        request.sources.push(SourceInput::new(
            package.clone(),
            LogicalPath::parse(*path).unwrap(),
            source.as_bytes(),
        ));
    }
    request
}

fn request_with_dependency(root: &str, package: &str, source: &str) -> CompilationRequest {
    let mut request = request(root);
    request.sources.push(SourceInput::new(
        PackageKey(package.into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        source.as_bytes(),
    ));
    request
}

fn text_runtime_manifest() -> RuntimeManifestInput {
    RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        host_imports: vec![],
        selectors: vec![
            PrimitiveSelector {
                role: PrimitiveRole::BranchBool,
                module_path: "crate".into(),
                name: "branch_bool".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextByteLen,
                module_path: "crate".into(),
                name: "__g1_text_byte_len".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextConcat,
                module_path: "crate".into(),
                name: "__g1_text_concat".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextEq,
                module_path: "crate".into(),
                name: "__g1_text_eq".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextFromUtf8Checked,
                module_path: "crate".into(),
                name: "__g1_text_from_utf8_checked".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextAsBytes,
                module_path: "crate".into(),
                name: "__g1_text_as_bytes".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::CharFromU32Checked,
                module_path: "crate".into(),
                name: "__g1_char_from_u32_checked".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::CharToU32,
                module_path: "crate".into(),
                name: "__g1_char_to_u32".into(),
            },
        ],
    }
}

fn char_runtime_manifest() -> RuntimeManifestInput {
    RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        host_imports: vec![],
        selectors: [
            (
                PrimitiveRole::CharFromU32Checked,
                "__g1_char_from_u32_checked",
            ),
            (PrimitiveRole::CharToU32, "__g1_char_to_u32"),
        ]
        .into_iter()
        .map(|(role, name)| PrimitiveSelector {
            role,
            module_path: "crate".into(),
            name: name.into(),
        })
        .collect(),
    }
}

fn bytes_runtime_manifest() -> RuntimeManifestInput {
    RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        host_imports: vec![],
        selectors: [
            (PrimitiveRole::TextByteLen, "__g1_text_byte_len"),
            (PrimitiveRole::TextAsBytes, "__g1_text_as_bytes"),
            (PrimitiveRole::BytesLen, "__g1_bytes_len"),
            (PrimitiveRole::BytesConcat, "__g1_bytes_concat"),
            (PrimitiveRole::BytesGet, "__g1_bytes_get"),
            (PrimitiveRole::BytesSlice, "__g1_bytes_slice"),
            (
                PrimitiveRole::BytesFromArrayMove,
                "__g1_bytes_from_array_move",
            ),
            (PrimitiveRole::BytesToArray, "__g1_bytes_to_array"),
            (
                PrimitiveRole::BytesUtf8ValidUpTo,
                "__g1_bytes_utf8_valid_up_to",
            ),
        ]
        .into_iter()
        .map(|(role, name)| PrimitiveSelector {
            role,
            module_path: "crate".into(),
            name: name.into(),
        })
        .collect(),
    }
}

fn text_bytes_runtime_manifest() -> RuntimeManifestInput {
    RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        host_imports: vec![],
        selectors: [
            (PrimitiveRole::TextByteLen, "__g1_text_byte_len"),
            (PrimitiveRole::TextConcat, "__g1_text_concat"),
            (PrimitiveRole::TextEq, "__g1_text_eq"),
            (
                PrimitiveRole::TextFromUtf8Checked,
                "__g1_text_from_utf8_checked",
            ),
            (PrimitiveRole::TextAsBytes, "__g1_text_as_bytes"),
            (
                PrimitiveRole::CharFromU32Checked,
                "__g1_char_from_u32_checked",
            ),
            (PrimitiveRole::CharToU32, "__g1_char_to_u32"),
            (PrimitiveRole::BytesLen, "__g1_bytes_len"),
            (PrimitiveRole::BytesConcat, "__g1_bytes_concat"),
            (PrimitiveRole::BytesGet, "__g1_bytes_get"),
            (PrimitiveRole::BytesSlice, "__g1_bytes_slice"),
            (
                PrimitiveRole::BytesFromArrayMove,
                "__g1_bytes_from_array_move",
            ),
            (PrimitiveRole::BytesToArray, "__g1_bytes_to_array"),
            (
                PrimitiveRole::BytesUtf8ValidUpTo,
                "__g1_bytes_utf8_valid_up_to",
            ),
        ]
        .into_iter()
        .map(|(role, name)| PrimitiveSelector {
            role,
            module_path: "crate".into(),
            name: name.into(),
        })
        .collect(),
    }
}

fn u32_runtime_manifest() -> RuntimeManifestInput {
    RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        host_imports: vec![],
        selectors: [
            (PrimitiveRole::CharToU32, "__g1_char_to_u32"),
            (PrimitiveRole::U32CheckedAdd, "__g1_u32_checked_add"),
            (PrimitiveRole::U32CheckedSub, "__g1_u32_checked_sub"),
            (PrimitiveRole::U32CheckedMul, "__g1_u32_checked_mul"),
            (PrimitiveRole::U32CheckedDiv, "__g1_u32_checked_div"),
            (PrimitiveRole::U32CheckedRem, "__g1_u32_checked_rem"),
            (PrimitiveRole::U32WrappingAdd, "__g1_u32_wrapping_add"),
            (PrimitiveRole::U32WrappingSub, "__g1_u32_wrapping_sub"),
            (PrimitiveRole::U32WrappingMul, "__g1_u32_wrapping_mul"),
            (PrimitiveRole::U32WrappingShl, "__g1_u32_wrapping_shl"),
            (PrimitiveRole::U32WrappingShr, "__g1_u32_wrapping_shr"),
            (PrimitiveRole::U32CheckedShl, "__g1_u32_checked_shl"),
            (PrimitiveRole::U32CheckedShr, "__g1_u32_checked_shr"),
            (PrimitiveRole::U32Eq, "__g1_u32_eq"),
            (PrimitiveRole::U32Lt, "__g1_u32_lt"),
            (PrimitiveRole::U32Le, "__g1_u32_le"),
            (PrimitiveRole::U32ToUsize, "__g1_u32_to_usize"),
            (
                PrimitiveRole::UsizeToU32Checked,
                "__g1_usize_to_u32_checked",
            ),
        ]
        .into_iter()
        .map(|(role, name)| PrimitiveSelector {
            role,
            module_path: "crate".into(),
            name: name.into(),
        })
        .collect(),
    }
}

fn int_runtime_manifest(role: PrimitiveRole, name: &str) -> RuntimeManifestInput {
    RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role,
            module_path: "crate".into(),
            name: name.into(),
        }],
    }
}

#[test]
fn manifest_bound_float_finiteness_predicates_execute_through_unsigned_vm_paths() {
    for (name, float, integer, to_bits, from_bits, infinity_bits) in [
        (
            "f32",
            "f32",
            "u32",
            "__g1_f32_to_bits",
            "__g1_f32_from_bits",
            "2139095040",
        ),
        (
            "f64",
            "f64",
            "u64",
            "__g1_f64_to_bits",
            "__g1_f64_from_bits",
            "9218868437227405312",
        ),
    ] {
        let source = format!(
            "fn {to_bits}(value: {float}) -> {integer} {{ () }}\
             fn {from_bits}(value: {integer}) -> {float} {{ () }}\
             fn __g1_int_bit_and<T>(left: T, right: T) -> T {{ () }}\
             fn bit_and<T>(left: T, right: T) -> T {{\
                 __g1_int_bit_and(move left, move right)\
             }}\
             finite(value: {float}) -> Bool {{\
                 bit_and({to_bits}(move value), {infinity_bits}) != {infinity_bits}\
             }}\
             pub fn main() -> Bool {{ finite({from_bits}({infinity_bits})) }}",
        );
        let mut input = request(&source);
        input.runtime_manifest = Some(RuntimeManifestInput {
            standard_library: PackageKey("app@0.1.0".into()),
            host_imports: vec![],
            selectors: [
                (format!("{name}-to-bits"), to_bits),
                (format!("{name}-from-bits"), from_bits),
                ("int-bit-and".into(), "__g1_int_bit_and"),
            ]
            .into_iter()
            .map(|(selector, declaration)| PrimitiveSelector {
                role: PrimitiveRole::parse_selector_name(&selector)
                    .expect("canonical primitive role"),
                module_path: "crate".into(),
                name: declaration.into(),
            })
            .collect(),
        });
        let artifact = StageZeroCompiler::new()
            .compile(input)
            .unwrap_or_else(|diagnostics| panic!("{name}: {diagnostics:#?}"))
            .artifact
            .expect("build must publish a VM artifact");
        assert!(
            !artifact.run_bool().unwrap(),
            "{name} infinity is not finite"
        );
        let program = decode_program(&artifact.canonical_bytes()).unwrap();
        assert!(program.functions.values().any(|function| {
            function.instructions.iter().any(|instruction| {
                matches!(
                    instruction,
                    VmInstruction::BitAndU32 { .. }
                        | VmInstruction::BitAndU64 { .. }
                        | VmInstruction::IntIntrinsic {
                            primitive: PrimitiveRole::IntBitAnd,
                            scalar: grandiose_stage0::ScalarType::U32
                                | grandiose_stage0::ScalarType::U64,
                            ..
                        }
                )
            })
        }));
    }
}

#[test]
fn manifest_bound_generic_int_wrapping_add_uses_distinct_wrapping_vm_semantics() {
    let mut input = request(
        "fn __g1_int_wrapping_add<T>(left: T, right: T) -> T { () } pub fn main() -> i64 { __g1_int_wrapping_add<i64>(9223372036854775807, 1) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntWrappingAdd,
        "__g1_int_wrapping_add",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic int declaration must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_i64().unwrap(), i64::MIN);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::WrappingAddI64 { .. }))
    }));
}

#[test]
fn public_generic_integer_wrappers_cover_all_width_runtime_semantics() {
    let compile = |source: String, role, name: &str| {
        let mut input = request(&source);
        input.runtime_manifest = Some(int_runtime_manifest(role, name));
        StageZeroCompiler::new()
            .compile(input)
            .unwrap_or_else(|diagnostics| panic!("{name}: {diagnostics:#?}"))
            .artifact
            .expect("build must publish a VM artifact")
    };

    let add = compile(
        "fn __g1_int_wrapping_add<T>(left: T, right: T) -> T { () } \
         pub fn add<T>(left: T, right: T) -> T { __g1_int_wrapping_add(move left, move right) } \
         pub fn main() -> u16 { add(65535, 1) }"
            .into(),
        PrimitiveRole::IntWrappingAdd,
        "__g1_int_wrapping_add",
    );
    assert_eq!(add.run_u16().unwrap(), 0);

    let bitwise = compile(
        "fn __g1_int_bit_xor<T>(left: T, right: T) -> T { () } \
         pub fn xor<T>(left: T, right: T) -> T { __g1_int_bit_xor(move left, move right) } \
         pub fn main() -> u128 { xor(340282366920938463463374607431768211455, 1) }"
            .into(),
        PrimitiveRole::IntBitXor,
        "__g1_int_bit_xor",
    );
    assert_eq!(bitwise.run_u128().unwrap(), u128::MAX - 1);

    let comparison = compile(
        "fn __g1_int_less<T>(left: T, right: T) -> u32 { () } \
         pub fn less<T>(left: T, right: T) -> u32 { __g1_int_less(move left, move right) } \
         pub fn low() -> i8 { 7 } pub fn high() -> i8 { 9 } \
         pub fn main() -> u32 { less(low(), high()) }"
            .into(),
        PrimitiveRole::IntLess,
        "__g1_int_less",
    );
    assert_eq!(comparison.run_u32().unwrap(), 1);

    let wrapping = compile(
        "fn __g1_int_convert_wrapping_to_i8<T>(value: T) -> i8 { () } \
         pub fn narrow<T>(value: T) -> i8 { __g1_int_convert_wrapping_to_i8(move value) } \
         pub fn maximum() -> u128 { 340282366920938463463374607431768211455 } \
         pub fn main() -> i8 { narrow(maximum()) }"
            .into(),
        PrimitiveRole::IntConvertWrappingToI8,
        "__g1_int_convert_wrapping_to_i8",
    );
    assert_eq!(wrapping.run_i8().unwrap(), -1);

    let checked = compile(
        "fn __g1_int_convert_checked_to_u8<T>(value: T) -> u8 { () } \
         pub fn narrow<T>(value: T) -> u8 { __g1_int_convert_checked_to_u8(move value) } \
         pub fn maximum() -> u128 { 340282366920938463463374607431768211455 } \
         pub fn main() -> u8 { narrow(maximum()) }"
            .into(),
        PrimitiveRole::IntConvertCheckedToU8,
        "__g1_int_convert_checked_to_u8",
    );
    assert!(matches!(
        checked.run_u8(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));

    let program = decode_program(&bitwise.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function.instructions.iter().any(|instruction| {
            matches!(
                instruction,
                VmInstruction::IntIntrinsic {
                    primitive: PrimitiveRole::IntBitXor,
                    scalar: grandiose_stage0::ScalarType::U128,
                    ..
                }
            )
        })
    }));
    let mut forged = program;
    let (function_key, destination) = forged
        .functions
        .iter()
        .find_map(|(key, function)| {
            function
                .instructions
                .iter()
                .find_map(|instruction| match instruction {
                    VmInstruction::IntIntrinsic { dst, .. } => Some((*key, *dst)),
                    _ => None,
                })
        })
        .expect("generic wrapper materialized an integer intrinsic");
    forged
        .functions
        .get_mut(&function_key)
        .expect("selected intrinsic belongs to its decoded function")
        .registers[destination as usize] = VmType::U64;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(
        decode_and_verify_program(&encode_program(&forged)).is_err(),
        "the verifier must reject a forged integer intrinsic result width"
    );
}

#[test]
fn manifest_bound_generic_int_wrapping_sub_uses_distinct_wrapping_vm_semantics() {
    let mut input = request(
        "fn __g1_int_wrapping_sub<T>(left: T, right: T) -> T { () } pub fn main() -> i64 { __g1_int_wrapping_sub<i64>(-9223372036854775807, 2) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntWrappingSub,
        "__g1_int_wrapping_sub",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic int declaration must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_i64().unwrap(), i64::MAX);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::WrappingSubI64 { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_wrapping_mul_uses_distinct_wrapping_vm_semantics() {
    let mut input = request(
        "fn __g1_int_wrapping_mul<T>(left: T, right: T) -> T { () } pub fn main() -> i64 { __g1_int_wrapping_mul<i64>(9223372036854775807, 2) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntWrappingMul,
        "__g1_int_wrapping_mul",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic int declaration must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_i64().unwrap(), -2);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::WrappingMulI64 { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_wrapping_neg_uses_wrapping_vm_semantics() {
    let mut input = request(
        "fn __g1_int_wrapping_neg<T>(value: T) -> T { () } pub fn main() -> i64 { __g1_int_wrapping_neg<i64>(-9223372036854775807 - 1) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntWrappingNeg,
        "__g1_int_wrapping_neg",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic int declaration must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_i64().unwrap(), i64::MIN);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::WrappingSubI64 { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_predicates_preserve_their_u32_runtime_abi() {
    for (role, name, body) in [
        (
            PrimitiveRole::IntEqual,
            "__g1_int_equal",
            "__g1_int_equal<i64>(7, 7)",
        ),
        (
            PrimitiveRole::IntLess,
            "__g1_int_less",
            "__g1_int_less<i64>(-1, 0)",
        ),
        (
            PrimitiveRole::IntGreater,
            "__g1_int_greater",
            "__g1_int_greater<i64>(0, -1)",
        ),
    ] {
        let mut input = request(&format!(
            "fn {name}<T>(left: T, right: T) -> u32 {{ () }} pub fn main() -> u32 {{ {body} }}"
        ));
        input.runtime_manifest = Some(int_runtime_manifest(role, name));
        assert_eq!(
            StageZeroCompiler::new()
                .compile(input)
                .unwrap()
                .artifact
                .unwrap()
                .run_u32()
                .unwrap(),
            1
        );
    }
}

#[test]
fn manifest_bound_checked_i64_to_usize_converts() {
    let mut input = request(
        "fn __g1_int_convert_checked_to_usize<T>(value: T) -> usize { () } pub fn main() -> usize { __g1_int_convert_checked_to_usize<i64>(42) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToUsize,
        "__g1_int_convert_checked_to_usize",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_usize()
            .unwrap(),
        42
    );
}

#[test]
fn manifest_bound_checked_i64_to_u8_converts() {
    let mut input = request(
        "fn __g1_int_convert_checked_to_u8<T>(value: T) -> u8 { () } pub fn main() -> u8 { __g1_int_convert_checked_to_u8<i64>(255) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToU8,
        "__g1_int_convert_checked_to_u8",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_u8()
            .unwrap(),
        255
    );
}

#[test]
fn manifest_bound_checked_i64_to_u16_converts() {
    let mut input = request(
        "fn __g1_int_convert_checked_to_u16<T>(value: T) -> u16 { () } pub fn main() -> u16 { __g1_int_convert_checked_to_u16<i64>(65535) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToU16,
        "__g1_int_convert_checked_to_u16",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_u16()
            .unwrap(),
        65_535
    );
}

#[test]
fn manifest_bound_checked_i64_to_i16_converts() {
    let mut input = request(
        "fn __g1_int_convert_checked_to_i16<T>(value: T) -> i16 { () } pub fn main() -> i16 { __g1_int_convert_checked_to_i16<i64>(-32768) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToI16,
        "__g1_int_convert_checked_to_i16",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_i16()
            .unwrap(),
        -32_768
    );
}

#[test]
fn manifest_bound_checked_i64_to_i32_converts_and_rejects_out_of_range_values() {
    let mut input = request(
        "fn __g1_int_convert_checked_to_i32<T>(value: T) -> i32 { () } pub fn main() -> i32 { __g1_int_convert_checked_to_i32<i64>(-2147483648) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToI32,
        "__g1_int_convert_checked_to_i32",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_i32()
            .unwrap(),
        i32::MIN
    );

    let mut overflow = request(
        "fn __g1_int_convert_checked_to_i32<T>(value: T) -> i32 { () } pub fn main() -> i32 { __g1_int_convert_checked_to_i32<i64>(2147483648) }",
    );
    overflow.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToI32,
        "__g1_int_convert_checked_to_i32",
    ));
    assert!(matches!(
        StageZeroCompiler::new()
            .compile(overflow)
            .unwrap()
            .artifact
            .unwrap()
            .run_i32(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
}

#[test]
fn manifest_bound_checked_i64_to_i8_converts_and_rejects_out_of_range_values() {
    let mut input = request(
        "fn __g1_int_convert_checked_to_i8<T>(value: T) -> i8 { () } pub fn main() -> i8 { __g1_int_convert_checked_to_i8<i64>(-128) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToI8,
        "__g1_int_convert_checked_to_i8",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_i8()
            .unwrap(),
        i8::MIN
    );
    let mut overflow = request(
        "fn __g1_int_convert_checked_to_i8<T>(value: T) -> i8 { () } pub fn main() -> i8 { __g1_int_convert_checked_to_i8<i64>(128) }",
    );
    overflow.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToI8,
        "__g1_int_convert_checked_to_i8",
    ));
    assert!(matches!(
        StageZeroCompiler::new()
            .compile(overflow)
            .unwrap()
            .artifact
            .unwrap()
            .run_i8(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
}

#[test]
fn manifest_bound_checked_i64_to_u64_converts_and_rejects_negative_values() {
    let mut input = request(
        "fn __g1_int_convert_checked_to_u64<T>(value: T) -> u64 { () } pub fn main() -> u64 { __g1_int_convert_checked_to_u64<i64>(9223372036854775807) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToU64,
        "__g1_int_convert_checked_to_u64",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_u64()
            .unwrap(),
        i64::MAX as u64
    );
    let mut negative = request(
        "fn __g1_int_convert_checked_to_u64<T>(value: T) -> u64 { () } pub fn main() -> u64 { __g1_int_convert_checked_to_u64<i64>(-1) }",
    );
    negative.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToU64,
        "__g1_int_convert_checked_to_u64",
    ));
    assert!(matches!(
        StageZeroCompiler::new()
            .compile(negative)
            .unwrap()
            .artifact
            .unwrap()
            .run_u64(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
}

#[test]
fn manifest_bound_checked_i64_to_u128_converts_and_rejects_negative_values() {
    let mut input = request(
        "fn __g1_int_convert_checked_to_u128<T>(value: T) -> u128 { () } pub fn main() -> u128 { __g1_int_convert_checked_to_u128<i64>(42) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToU128,
        "__g1_int_convert_checked_to_u128",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_u128()
            .unwrap(),
        42
    );
}

#[test]
fn manifest_bound_checked_i64_to_i128_preserves_signed_value() {
    let mut input = request(
        "fn __g1_int_convert_checked_to_i128<T>(value: T) -> i128 { () } pub fn main() -> i128 { __g1_int_convert_checked_to_i128<i64>(-42) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToI128,
        "__g1_int_convert_checked_to_i128",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_i128()
            .unwrap(),
        -42
    );
}

#[test]
fn manifest_bound_wrapping_i64_to_i128_preserves_signed_value() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_i128<T>(value: T) -> i128 { () } pub fn main() -> i128 { __g1_int_convert_wrapping_to_i128<i64>(-42) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToI128,
        "__g1_int_convert_wrapping_to_i128",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_i128()
            .unwrap(),
        -42
    );
}

#[test]
fn manifest_bound_wrapping_i64_to_u128_retains_twos_complement_bits() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_u128<T>(value: T) -> u128 { () } pub fn main() -> u128 { __g1_int_convert_wrapping_to_u128<i64>(-1) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToU128,
        "__g1_int_convert_wrapping_to_u128",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_u128()
            .unwrap(),
        u128::MAX
    );
}

#[test]
fn manifest_bound_checked_i64_to_isize_preserves_the_frozen_signed_width() {
    let mut input = request(
        "fn __g1_int_convert_checked_to_isize<T>(value: T) -> isize { () } pub fn main() -> isize { __g1_int_convert_checked_to_isize<i64>(-42) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToIsize,
        "__g1_int_convert_checked_to_isize",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_isize()
            .unwrap(),
        -42
    );
}

#[test]
fn manifest_bound_wrapping_i64_to_isize_preserves_twos_complement_bits() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_isize<T>(value: T) -> isize { () } pub fn main() -> isize { __g1_int_convert_wrapping_to_isize<i64>(-42) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToIsize,
        "__g1_int_convert_wrapping_to_isize",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_isize()
            .unwrap(),
        -42
    );
}

#[test]
fn manifest_bound_wrapping_i64_to_u64_retains_twos_complement_bits() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_u64<T>(value: T) -> u64 { () } pub fn main() -> u64 { __g1_int_convert_wrapping_to_u64<i64>(-1) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToU64,
        "__g1_int_convert_wrapping_to_u64",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_u64()
            .unwrap(),
        u64::MAX
    );
}

#[test]
fn manifest_bound_wrapping_i64_to_i8_truncates_twos_complement_bits() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_i8<T>(value: T) -> i8 { () } pub fn main() -> i8 { __g1_int_convert_wrapping_to_i8<i64>(255) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToI8,
        "__g1_int_convert_wrapping_to_i8",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_i8()
            .unwrap(),
        -1
    );
}

#[test]
fn manifest_bound_generic_int_wrapping_to_i32_truncates_twos_complement_bits() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_i32<T>(value: T) -> i32 { () } pub fn main() -> i32 { __g1_int_convert_wrapping_to_i32<i64>(4294967295) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToI32,
        "__g1_int_convert_wrapping_to_i32",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("wrapping i32 conversion must specialize")
        .artifact
        .expect("entry must emit an artifact");
    assert_eq!(artifact.run_i32().unwrap(), -1);
}

#[test]
fn manifest_bound_checked_i64_to_u32_converts_and_rejects_out_of_range_values() {
    let source = "fn __g1_int_convert_checked_to_u32<T>(value: T) -> u32 { () } pub fn main() -> u32 { __g1_int_convert_checked_to_u32<i64>(42) }";
    let mut input = request(source);
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertCheckedToU32,
        "__g1_int_convert_checked_to_u32",
    ));
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .unwrap()
            .run_u32()
            .unwrap(),
        42
    );
}

#[test]
fn manifest_bound_generic_int_shr_uses_its_mixed_vm_abi() {
    let mut input = request(
        "fn __g1_int_shr<T>(value: T, count: u32) -> T { () } fn __g1_int_equal<T>(left: T, right: T) -> u32 { () } pub fn main() -> i64 { __g1_int_shr<i64>(8, __g1_int_equal<i64>(65, 65)) }",
    );
    input.runtime_manifest = Some(RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        host_imports: vec![],
        selectors: vec![
            PrimitiveSelector {
                role: PrimitiveRole::IntShr,
                module_path: "crate".into(),
                name: "__g1_int_shr".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::IntEqual,
                module_path: "crate".into(),
                name: "__g1_int_equal".into(),
            },
        ],
    });
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic int declaration must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_i64().unwrap(), 4);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::IntShrI64 { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_bit_xor_uses_distinct_bitwise_vm_semantics() {
    let mut input = request(
        "fn __g1_int_bit_xor<T>(left: T, right: T) -> T { () } pub fn main() -> i64 { __g1_int_bit_xor<i64>(42, 15) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntBitXor,
        "__g1_int_bit_xor",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic int declaration must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_i64().unwrap(), 37);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::BitXorI64 { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_bit_and_uses_distinct_bitwise_vm_semantics() {
    let mut input = request(
        "fn __g1_int_bit_and<T>(left: T, right: T) -> T { () } pub fn main() -> i64 { __g1_int_bit_and<i64>(42, 15) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntBitAnd,
        "__g1_int_bit_and",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic int declaration must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_i64().unwrap(), 10);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::BitAndI64 { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_bit_or_uses_distinct_bitwise_vm_semantics() {
    let mut input = request(
        "fn __g1_int_bit_or<T>(left: T, right: T) -> T { () } pub fn main() -> i64 { __g1_int_bit_or<i64>(40, 3) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntBitOr,
        "__g1_int_bit_or",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic int declaration must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_i64().unwrap(), 43);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::BitOrI64 { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_bit_not_uses_distinct_unary_vm_semantics() {
    let mut input = request(
        "fn __g1_int_bit_not<T>(value: T) -> T { () } pub fn main() -> i64 { __g1_int_bit_not<i64>(10) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntBitNot,
        "__g1_int_bit_not",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact unary generic int declaration must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_i64().unwrap(), !10);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::BitNotI64 { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_shift_left_rejects_an_i64_width_count() {
    let mut input = request(
        "fn __g1_char_to_u32(value: char) -> u32 { () } fn __g1_int_shl<T>(value: T, count: u32) -> T { () } pub fn main() -> i64 { __g1_int_shl<i64>(1, __g1_char_to_u32('@')) }",
    );
    input.runtime_manifest = Some(RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        host_imports: vec![],
        selectors: vec![
            PrimitiveSelector {
                role: PrimitiveRole::CharToU32,
                module_path: "crate".into(),
                name: "__g1_char_to_u32".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::IntShl,
                module_path: "crate".into(),
                name: "__g1_int_shl".into(),
            },
        ],
    });
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic shift-left declaration must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert!(matches!(
        artifact.run_i64(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::ShlI64 { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_wrapping_to_u32_truncates_twos_complement_bits() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_u32<T>(value: T) -> u32 { () } pub fn main() -> u32 { __g1_int_convert_wrapping_to_u32<i64>(-1) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToU32,
        "__g1_int_convert_wrapping_to_u32",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic wrapping conversion must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_u32().unwrap(), u32::MAX);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::I64ToU32Wrapping { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_wrapping_to_usize_truncates_twos_complement_bits() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_usize<T>(value: T) -> usize { () } pub fn main() -> usize { __g1_int_convert_wrapping_to_usize<i64>(-1) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToUsize,
        "__g1_int_convert_wrapping_to_usize",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic wrapping conversion must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_usize().unwrap(), u64::MAX);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::I64ToUsizeWrapping { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_wrapping_to_u8_truncates_twos_complement_bits() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_u8<T>(value: T) -> u8 { () } pub fn main() -> u8 { __g1_int_convert_wrapping_to_u8<i64>(-1) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToU8,
        "__g1_int_convert_wrapping_to_u8",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic wrapping conversion must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_u8().unwrap(), u8::MAX);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::I64ToU8Wrapping { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_wrapping_to_u16_truncates_twos_complement_bits() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_u16<T>(value: T) -> u16 { () } pub fn main() -> u16 { __g1_int_convert_wrapping_to_u16<i64>(-1) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToU16,
        "__g1_int_convert_wrapping_to_u16",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("the exact generic wrapping conversion must specialize for frozen i64")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_u16().unwrap(), u16::MAX);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::I64ToU16Wrapping { .. }))
    }));
}

#[test]
fn manifest_bound_generic_int_wrapping_to_i16_truncates_twos_complement_bits() {
    let mut input = request(
        "fn __g1_int_convert_wrapping_to_i16<T>(value: T) -> i16 { () } pub fn main() -> i16 { __g1_int_convert_wrapping_to_i16<i64>(65535) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntConvertWrappingToI16,
        "__g1_int_convert_wrapping_to_i16",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("wrapping i16 conversion must specialize")
        .artifact
        .expect("VM artifact");
    assert_eq!(artifact.run_i16().unwrap(), -1);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::I64ToI16Wrapping { .. }))
    }));
}

const TEXT_RUNTIME_LEAVES: &str = "pub fn branch_bool<T>(condition: Bool, on_true: () -> T, on_false: () -> T) -> T { let ignored = on_true(); on_false() } pub fn __g1_text_byte_len(value: Text) -> usize { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () } ";

const PRIVATE_TEXT_RUNTIME_LEAVES: &str = "fn branch_bool<T>(condition: Bool, on_true: () -> T, on_false: () -> T) -> T { let ignored = on_true(); on_false() } fn __g1_text_byte_len(value: Text) -> usize { () } fn __g1_text_concat(left: Text, right: Text) -> Text { () } fn __g1_text_eq(left: Text, right: Text) -> u32 { () } fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } fn __g1_text_as_bytes(value: Text) -> Bytes { () } fn __g1_char_from_u32_checked(value: u32) -> char { () } fn __g1_char_to_u32(value: char) -> u32 { () } ";

const BYTES_RUNTIME_LEAVES: &str = "pub fn __g1_text_byte_len(value: Text) -> usize { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_bytes_len(value: Bytes) -> usize { () } pub fn __g1_bytes_concat(left: Bytes, right: Bytes) -> Bytes { () } pub fn __g1_bytes_get(bytes: Bytes, index: usize) -> u8 { () } pub fn __g1_bytes_slice(bytes: Bytes, start: usize, end: usize) -> Bytes { () } pub fn __g1_bytes_from_array_move(value: Array<u8>) -> Bytes { () } pub fn __g1_bytes_to_array(value: Bytes) -> Array<u8> { () } pub fn __g1_bytes_utf8_valid_up_to(value: Bytes) -> usize { () } ";

const TEXT_BYTES_RUNTIME_LEAVES: &str = "pub fn __g1_text_byte_len(value: Text) -> usize { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () } pub fn __g1_bytes_len(value: Bytes) -> usize { () } pub fn __g1_bytes_concat(left: Bytes, right: Bytes) -> Bytes { () } pub fn __g1_bytes_get(bytes: Bytes, index: usize) -> u8 { () } pub fn __g1_bytes_slice(bytes: Bytes, start: usize, end: usize) -> Bytes { () } pub fn __g1_bytes_from_array_move(value: Array<u8>) -> Bytes { () } pub fn __g1_bytes_to_array(value: Bytes) -> Array<u8> { () } pub fn __g1_bytes_utf8_valid_up_to(value: Bytes) -> usize { () } ";

const ARRAY_RUNTIME_LEAVES: &str = "pub fn __g1_array_new<T>(length: usize, fill: T) -> Array<T> where T: Use<[0, *]> { () } pub fn __g1_array_len<T>(value: &Array<T>) -> usize { () } pub fn __g1_array_get_copy<T>(value: &Array<T>, index: usize) -> T where T: Use<[0, *]> { () } pub fn __g1_array_get_move<T>(value: &mut Array<T>, index: usize) -> T { () } pub fn __g1_array_get_borrow_shared<T>(value: &Array<T>, index: usize) -> &T { () } pub fn __g1_array_get_borrow_unique<T>(value: &mut Array<T>, index: usize) -> &mut T { () } pub fn __g1_array_set_move<T>(value: &mut Array<T>, index: usize, item: T) { () } pub fn __g1_array_empty<T>() -> Array<T> { () } pub fn __g1_array_push_move<T>(value: &mut Array<T>, item: T) { () } pub fn __g1_array_pop_move<T>(value: &mut Array<T>) -> T { () } pub fn __g1_array_capacity<T>(value: &Array<T>) -> usize { () } pub fn __g1_array_reserve<T>(value: &mut Array<T>, additional: usize) { () } pub fn __g1_array_finish_drained<T>(value: Array<T>) { () } ";

fn array_runtime_manifest() -> RuntimeManifestInput {
    RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        host_imports: vec![],
        selectors: [
            (PrimitiveRole::ArrayNew, "__g1_array_new"),
            (PrimitiveRole::ArrayLen, "__g1_array_len"),
            (PrimitiveRole::ArrayGetCopy, "__g1_array_get_copy"),
            (PrimitiveRole::ArrayGetMove, "__g1_array_get_move"),
            (
                PrimitiveRole::ArrayGetBorrowShared,
                "__g1_array_get_borrow_shared",
            ),
            (
                PrimitiveRole::ArrayGetBorrowUnique,
                "__g1_array_get_borrow_unique",
            ),
            (PrimitiveRole::ArraySetMove, "__g1_array_set_move"),
            (PrimitiveRole::ArrayEmpty, "__g1_array_empty"),
            (PrimitiveRole::ArrayPushMove, "__g1_array_push_move"),
            (PrimitiveRole::ArrayPopMove, "__g1_array_pop_move"),
            (PrimitiveRole::ArrayCapacity, "__g1_array_capacity"),
            (PrimitiveRole::ArrayReserve, "__g1_array_reserve"),
            (
                PrimitiveRole::ArrayFinishDrained,
                "__g1_array_finish_drained",
            ),
        ]
        .into_iter()
        .map(|(role, name)| PrimitiveSelector {
            role,
            module_path: "crate".into(),
            name: name.into(),
        })
        .collect(),
    }
}

#[test]
fn manifest_bound_array_storage_leaves_lower_and_execute() {
    let mut input = request(&format!(
        "{ARRAY_RUNTIME_LEAVES} pub fn main() -> usize {{ let value = __g1_array_empty<i64>(); __g1_array_len(&value) }}"
    ));
    input.runtime_manifest = Some(array_runtime_manifest());
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("trusted Array leaves must bind")
        .artifact
        .expect("VM artifact");
    assert_eq!(artifact.run_usize().unwrap(), 0);
    assert!(
        decode_program(&artifact.canonical_bytes())
            .unwrap()
            .functions
            .values()
            .any(|function| function
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::ArrayEmpty { .. })))
    );
}

const U32_RUNTIME_LEAVES: &str = "pub fn __g1_char_to_u32(value: char) -> u32 { () } pub fn __g1_u32_checked_add(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_checked_sub(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_checked_mul(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_checked_div(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_checked_rem(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_wrapping_add(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_wrapping_sub(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_wrapping_mul(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_wrapping_shl(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_wrapping_shr(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_checked_shl(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_checked_shr(left: u32, right: u32) -> u32 { () } pub fn __g1_u32_eq(left: u32, right: u32) -> Bool { () } pub fn __g1_u32_lt(left: u32, right: u32) -> Bool { () } pub fn __g1_u32_le(left: u32, right: u32) -> Bool { () } pub fn __g1_u32_to_usize(value: u32) -> usize { () } pub fn __g1_usize_to_u32_checked(value: usize) -> u32 { () } ";

#[test]
fn manifest_binds_private_standard_library_leaves_by_exact_identity() {
    let mut input = request(&format!(
        "{PRIVATE_TEXT_RUNTIME_LEAVES} pub fn main() -> usize {{ __g1_text_byte_len(\"a🦀\") }}"
    ));
    input.runtime_manifest = Some(text_runtime_manifest());
    let outcome = StageZeroCompiler::new()
        .compile(input)
        .expect("a private trusted layer-1 leaf must lower through its manifest identity");
    assert_eq!(
        outcome
            .artifact
            .expect("build must publish a VM artifact")
            .run_usize()
            .unwrap(),
        5
    );
}

#[test]
fn manifest_bound_text_byte_len_leaf_lowers_to_the_capability_free_vm_opcode() {
    let mut input = request(&format!(
        "{TEXT_RUNTIME_LEAVES} pub fn main() -> usize {{ __g1_text_byte_len(\"a🦀\") }}"
    ));
    input.runtime_manifest = Some(text_runtime_manifest());
    let outcome = StageZeroCompiler::new().compile(input).unwrap();
    let artifact = outcome.artifact.expect("build must publish a VM artifact");
    assert_eq!(artifact.run_usize().unwrap(), 5);
}

#[test]
fn manifest_bound_text_family_executes_concat_equality_and_utf8_round_trip() {
    let mut text = request(&format!(
        "{TEXT_RUNTIME_LEAVES} pub fn main() -> Text {{ __g1_text_from_utf8_checked(__g1_text_as_bytes(__g1_text_concat(\"a\", \"🦀\"))) }}"
    ));
    text.runtime_manifest = Some(text_runtime_manifest());
    assert_eq!(
        StageZeroCompiler::new()
            .compile(text)
            .unwrap()
            .artifact
            .expect("build must publish a VM artifact")
            .run_text()
            .unwrap(),
        "a🦀"
    );

    let mut equality = request(&format!(
        "{TEXT_RUNTIME_LEAVES} pub fn main() -> u32 {{ __g1_text_eq(\"same\", \"same\") }}"
    ));
    equality.runtime_manifest = Some(text_runtime_manifest());
    assert_eq!(
        StageZeroCompiler::new()
            .compile(equality)
            .unwrap()
            .artifact
            .expect("build must publish a VM artifact")
            .run_u32()
            .unwrap(),
        1
    );
}

#[test]
fn manifest_bound_checked_char_family_round_trips_the_u32_abi() {
    let mut input = request(&format!(
        "{TEXT_RUNTIME_LEAVES} pub fn main() -> u32 {{ __g1_char_to_u32(__g1_char_from_u32_checked(__g1_text_eq(\"same\", \"same\"))) }}"
    ));
    input.runtime_manifest = Some(text_runtime_manifest());
    assert_eq!(
        StageZeroCompiler::new()
            .compile(input)
            .unwrap()
            .artifact
            .expect("build must publish a VM artifact")
            .run_u32()
            .unwrap(),
        1
    );
}

#[test]
fn public_char_helpers_preserve_unicode_scalar_boundaries_and_ordering() {
    const CHAR_HELPERS: &str = "\
        fn __g1_char_from_u32_checked(value: u32) -> char { () } \
        fn __g1_char_to_u32(value: char) -> u32 { () } \
        pub fn char_from_u32(value: u32) -> char { __g1_char_from_u32_checked(move value) } \
        pub fn char_to_u32(value: char) -> u32 { __g1_char_to_u32(move value) } ";

    for value in [0, 55295, 57344, 1114111] {
        let source = format!("{CHAR_HELPERS} pub fn main() -> char {{ char_from_u32({value}) }}");
        let mut input = request(&source);
        input.runtime_manifest = Some(char_runtime_manifest());
        let artifact = StageZeroCompiler::new()
            .compile(input)
            .expect("public Char helper must compile")
            .artifact
            .expect("build must publish a VM artifact");
        assert_eq!(artifact.run_char().unwrap(), char::from_u32(value).unwrap());
        let program = decode_program(&artifact.canonical_bytes()).unwrap();
        assert!(program.functions.values().any(|function| {
            function
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::CharFromU32Checked { .. }))
        }));
    }

    let mut round_trip = request(&format!(
        "{CHAR_HELPERS} pub fn main() -> u32 {{ char_to_u32(char_from_u32(128640)) }}"
    ));
    round_trip.runtime_manifest = Some(char_runtime_manifest());
    let artifact = StageZeroCompiler::new()
        .compile(round_trip)
        .expect("public Char conversion chain must compile")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_u32().unwrap(), 128640);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CharToU32 { .. }))
    }));

    let mut ordering = request(&format!(
        "{CHAR_HELPERS} pub fn main() -> Bool {{ char_from_u32(0) < char_from_u32(1114111) }}"
    ));
    ordering.runtime_manifest = Some(char_runtime_manifest());
    let artifact = StageZeroCompiler::new()
        .compile(ordering)
        .expect("Char comparison through public helpers must compile")
        .artifact
        .expect("build must publish a VM artifact");
    assert!(artifact.run_bool().unwrap());
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CompareChar { .. }))
    }));
}

#[test]
fn public_char_from_u32_rejects_surrogates_and_out_of_range_scalars() {
    const CHAR_HELPERS: &str = "\
        fn __g1_char_from_u32_checked(value: u32) -> char { () } \
        fn __g1_char_to_u32(value: char) -> u32 { () } \
        pub fn char_from_u32(value: u32) -> char { __g1_char_from_u32_checked(move value) } ";

    for value in [55296, 1114112] {
        let mut input = request(&format!(
            "{CHAR_HELPERS} pub fn main() -> char {{ char_from_u32({value}) }}"
        ));
        input.runtime_manifest = Some(char_runtime_manifest());
        let artifact = StageZeroCompiler::new()
            .compile(input)
            .expect("checked Char conversion is a runtime trap, not a compile failure")
            .artifact
            .expect("build must publish a VM artifact");
        assert!(
            matches!(artifact.run_char(), Err(VmArtifactError::InvalidChar { value: found }) if found == value),
            "invalid Unicode scalar {value:#x} must trap at the VM boundary"
        );
    }
}

#[test]
fn manifest_bound_bytes_family_round_trips_and_executes_checked_operations() {
    let mut round_trip = request(&format!(
        "{BYTES_RUNTIME_LEAVES} pub fn main() -> usize {{ __g1_bytes_utf8_valid_up_to(__g1_bytes_from_array_move(__g1_bytes_to_array(__g1_text_as_bytes(\"a🦀\")))) }}"
    ));
    round_trip.runtime_manifest = Some(bytes_runtime_manifest());
    assert_eq!(
        StageZeroCompiler::new()
            .compile(round_trip)
            .unwrap()
            .artifact
            .expect("build must publish a VM artifact")
            .run_usize()
            .unwrap(),
        5
    );

    let mut concat_and_slice = request(&format!(
        "{BYTES_RUNTIME_LEAVES} pub fn main() -> usize {{ __g1_bytes_len(__g1_bytes_slice(__g1_bytes_concat(__g1_text_as_bytes(\"a\"), __g1_text_as_bytes(\"🦀\")), __g1_text_byte_len(\"\"), __g1_text_byte_len(\"a🦀\"))) }}"
    ));
    concat_and_slice.runtime_manifest = Some(bytes_runtime_manifest());
    assert_eq!(
        StageZeroCompiler::new()
            .compile(concat_and_slice)
            .unwrap()
            .artifact
            .expect("build must publish a VM artifact")
            .run_usize()
            .unwrap(),
        5
    );

    let mut get = request(&format!(
        "{BYTES_RUNTIME_LEAVES} pub fn main() -> u8 {{ __g1_bytes_get(__g1_text_as_bytes(\"hi\"), __g1_text_byte_len(\"\")) }}"
    ));
    get.runtime_manifest = Some(bytes_runtime_manifest());
    assert_eq!(
        StageZeroCompiler::new()
            .compile(get)
            .unwrap()
            .artifact
            .expect("build must publish a VM artifact")
            .run_u8()
            .unwrap(),
        b'h'
    );
}

#[test]
fn public_text_bytes_helpers_preserve_utf8_and_array_ownership_across_calls() {
    let source = format!(
        "{TEXT_BYTES_RUNTIME_LEAVES} \
         pub fn text_concat(left: Text, right: Text) -> Text {{ __g1_text_concat(move left, move right) }} \
         pub fn text_bytes(value: Text) -> Bytes {{ __g1_text_as_bytes(move value) }} \
         pub fn text_from_bytes(value: Bytes) -> Text {{ __g1_text_from_utf8_checked(move value) }} \
         pub fn bytes_to_array(value: Bytes) -> Array<u8> {{ __g1_bytes_to_array(move value) }} \
         pub fn bytes_from_array(value: Array<u8>) -> Bytes {{ __g1_bytes_from_array_move(move value) }} \
         pub fn bytes_slice(value: Bytes, start: usize, end: usize) -> Bytes {{ __g1_bytes_slice(move value, start, end) }} \
         pub fn normalize(value: Text) -> Text {{ let bytes = text_bytes(value); let copied = bytes_to_array(bytes); text_from_bytes(bytes_from_array(move copied)) }} \
         pub fn main() -> Text {{ let joined = text_concat(\"a\", \"🦀\"); let bytes = text_bytes(joined); let slice = bytes_slice(bytes, __g1_text_byte_len(\"\"), __g1_text_byte_len(\"a🦀\")); normalize(text_from_bytes(slice)) }}"
    );
    let mut input = request(&source);
    input.runtime_manifest = Some(text_bytes_runtime_manifest());
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("public Text/Bytes wrappers must cross ordinary VM calls")
        .artifact
        .expect("build must publish a VM artifact");
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function.instructions.iter().any(|instruction| {
            matches!(
                instruction,
                VmInstruction::TextAsBytes { .. }
                    | VmInstruction::TextFromUtf8Checked { .. }
                    | VmInstruction::BytesToArray { .. }
                    | VmInstruction::BytesFromArrayMove { .. }
            )
        })
    }));
    assert_eq!(artifact.run_text().unwrap(), "a🦀");
}

#[test]
fn public_text_bytes_helpers_trap_on_invalid_utf8_and_byte_bounds() {
    // Both failures are dynamic: typed wrappers may publish their artifact,
    // but the sealed VM leaves reject malformed bytes and indexes at execution.
    let invalid_utf8 = format!(
        "{TEXT_BYTES_RUNTIME_LEAVES} \
         pub fn text_from_bytes(value: Bytes) -> Text {{ __g1_text_from_utf8_checked(move value) }} \
         pub fn bytes_from_array(value: Array<u8>) -> Bytes {{ __g1_bytes_from_array_move(move value) }} \
         pub fn invalid_array() -> Array<u8> {{ [255] }} \
         pub fn main() -> Text {{ text_from_bytes(bytes_from_array(invalid_array())) }}"
    );
    let mut input = request(&invalid_utf8);
    input.runtime_manifest = Some(text_bytes_runtime_manifest());
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("invalid UTF-8 is a checked runtime failure")
        .artifact
        .expect("build must publish a VM artifact");
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::ConstU8 { value: 255, .. }))
    }));
    let mut forged = program;
    let (function_key, constant) = forged
        .functions
        .iter()
        .find_map(|(key, function)| {
            function
                .instructions
                .iter()
                .find_map(|instruction| match instruction {
                    VmInstruction::ConstU8 { dst, .. } => Some((*key, *dst)),
                    _ => None,
                })
        })
        .expect("the invalid UTF-8 array contains a typed byte literal");
    forged
        .functions
        .get_mut(&function_key)
        .expect("selected function belongs to decoded program")
        .registers[constant as usize] = VmType::I64;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(
        decode_and_verify_program(&encode_program(&forged)).is_err(),
        "a ConstU8 destination must retain its byte register type"
    );
    assert!(matches!(
        artifact.run_text(),
        Err(VmArtifactError::InvalidUtf8)
    ));

    let out_of_bounds = format!(
        "{TEXT_BYTES_RUNTIME_LEAVES} \
         pub fn text_bytes(value: Text) -> Bytes {{ __g1_text_as_bytes(move value) }} \
         pub fn byte_at(value: Bytes, index: usize) -> u8 {{ __g1_bytes_get(move value, index) }} \
         pub fn main() -> u8 {{ byte_at(text_bytes(\"hi\"), __g1_text_byte_len(\"hi\")) }}"
    );
    let mut input = request(&out_of_bounds);
    input.runtime_manifest = Some(text_bytes_runtime_manifest());
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("out-of-bounds byte access is a runtime failure")
        .artifact
        .expect("build must publish a VM artifact");
    assert!(matches!(
        artifact.run_u8(),
        Err(VmArtifactError::InvalidRegister { .. })
    ));
}

#[test]
fn manifest_bound_u32_runtime_family_lowers_from_source_by_exact_identity() {
    let mut arithmetic = request(&format!(
        "{U32_RUNTIME_LEAVES} pub fn main() -> usize {{ __g1_u32_to_usize(__g1_u32_checked_add(__g1_char_to_u32('A'), __g1_char_to_u32('B'))) }}"
    ));
    arithmetic.runtime_manifest = Some(u32_runtime_manifest());
    assert_eq!(
        StageZeroCompiler::new()
            .compile(arithmetic)
            .unwrap()
            .artifact
            .expect("build must publish a VM artifact")
            .run_usize()
            .unwrap(),
        ('A' as u32 + 'B' as u32) as u64,
    );

    let mut comparison = request(&format!(
        "{U32_RUNTIME_LEAVES} pub fn main() -> Bool {{ __g1_u32_lt(__g1_char_to_u32('A'), __g1_char_to_u32('B')) }}"
    ));
    comparison.runtime_manifest = Some(u32_runtime_manifest());
    assert!(
        StageZeroCompiler::new()
            .compile(comparison)
            .unwrap()
            .artifact
            .expect("build must publish a VM artifact")
            .run_bool()
            .unwrap()
    );
}

#[test]
fn source_text_byte_len_spelling_is_not_opaque_without_manifest_identity() {
    let source = "pub fn __g1_text_byte_len(value: Text) -> usize { () } pub fn main() -> usize { __g1_text_byte_len(\"abc\") }";
    let error = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4110"),
        "an unbound source leaf must receive normal result-body checking: {:#?}",
        error.diagnostics()
    );
}

#[derive(Debug)]
struct SourceWorldFingerprint;

impl Query for SourceWorldFingerprint {
    type Key = ();
    type Value = Digest;
    type Error = ();

    const NAME: &'static str = "service_source_world_fingerprint";

    fn execute(
        &self,
        context: &mut QueryContext<'_>,
        (): Self::Key,
    ) -> Result<QueryValue<Self::Value>, QueryFailure<Self::Error>> {
        context.check()?;
        let fingerprint = context.snapshot().world().fingerprint;
        context.depend("source_world", fingerprint);
        Ok(QueryValue {
            value: fingerprint,
            fingerprint,
            completeness: QueryCompleteness::Complete,
        })
    }
}

#[test]
fn service_exposes_malformed_requests_as_structured_diagnostics() {
    let mut malformed = request("pub fn main() -> i64 { 0 }");
    malformed.sources.clear();

    let error = StageZeroCompiler::new().compile(malformed).unwrap_err();
    let diagnostics = error.diagnostics();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "G7015");
    assert_eq!(diagnostics[0].class, DiagnosticClass::Request);
    assert_eq!(diagnostics[0].severity, Severity::Error);
    assert!(diagnostics[0].primary.is_none());
    assert!(diagnostics[0].input_fingerprint.is_none());
}

#[test]
fn service_classifies_untrusted_source_bytes_as_input_corruption() {
    let mut malformed = request("pub fn main() -> i64 { 0 }");
    malformed.sources[0].bytes = vec![0xff].into();
    malformed.sources[0].digest = Digest::of_bytes(&[0xff]);

    let error = StageZeroCompiler::new().compile(malformed).unwrap_err();
    let diagnostics = error.diagnostics();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "G7018");
    assert_eq!(diagnostics[0].class, DiagnosticClass::InputCorruption);
    assert!(diagnostics[0].input_fingerprint.is_none());
}

#[test]
fn service_compiles_and_runs_a_verified_vm_artifact_from_an_immutable_request() {
    let outcome = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { 40 + 2 }"))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_compact_label_result_annotations_constrain_transfers() {
    let source = "pub fn main() -> i64 { @done: i64 { @done(42); 0 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let invalid = "pub fn main() -> i64 { @done: i64 { @done(true); 0 } }";
    let error = StageZeroCompiler::new()
        .compile(request(invalid))
        .unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4178"),
        "annotated label transfer mismatch was accepted: {:#?}",
        error.diagnostics()
    );
}

#[test]
fn service_compact_label_transfer_is_terminal_but_preserves_its_typed_result() {
    // The suffix is intentionally incompatible with the label result.  A
    // transfer exits the label, so neither type checking nor VM execution may
    // treat that suffix as a normal continuation of `@done(42)`.
    let source = "pub fn main() -> i64 { @done: i64 { @done(42); true } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("terminal compact label transfer must not type-check its dead suffix");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

}

#[test]
fn service_compact_label_cannot_escape_through_a_closure() {
    let source = "pub fn main() -> i64 { @done: i64 { let delayed = (value: i64) -> i64 { @done(value) }; 0 } }";
    let error = StageZeroCompiler::new()
        .compile(request(source))
        .expect_err("a compact label brand must not escape its lexical scope");
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4179"),
        "compact label escape was accepted: {:#?}",
        error.diagnostics()
    );
}

#[test]
fn service_accepts_symbolic_structural_const_layout_contracts() {
    let source = "pub struct Tag<n: u32> {} pub fn identity<n: u32>(value: Tag<n + 1>) -> Tag<1 + n> { value } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("a generic callable may carry canonical symbolic const layouts");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_host_imports_not_granted_by_the_frozen_request_manifest() {
    let error = StageZeroCompiler::new()
        .compile(request(
            "host clock fn now() -> i64; pub fn main() -> i64 { now() }",
        ))
        .unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G7032"),
        "{error:#?}"
    );
}

#[test]
fn service_emits_an_authorized_direct_host_import_without_an_ordinary_callee_body() {
    let mut input = request("host clock fn now() -> i64; pub fn main() -> i64 { now() }");
    input.capability_manifest.push("clock".into());
    let outcome = StageZeroCompiler::new().compile(input).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{outcome:#?}");
    let artifact = outcome
        .artifact
        .expect("authorized host import emits a program");
    assert!(matches!(
        artifact.run_i64(),
        Err(VmArtifactError::HostCallRequiresAuthority { capability, symbol })
            if capability == "clock" && symbol == "now"
    ));
}

#[test]
fn manifest_bound_host_placeholder_skips_seed_only_unit_body() {
    let mut input = request(
        "fn __g1_process_args_get() -> Array<Text> { () } pub fn main() -> Array<Text> { __g1_process_args_get() }",
    );
    input.capability_manifest.push("process_args".into());
    input.runtime_manifest = Some(RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        selectors: vec![],
        host_imports: vec![HostImportSelector {
            module_path: "crate".into(),
            name: "__g1_process_args_get".into(),
            capability: "process_args".into(),
            symbol: "__g1_process_args_get".into(),
        }],
    });

    let outcome = StageZeroCompiler::new().compile(input).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{outcome:#?}");
    let artifact = outcome
        .artifact
        .expect("host placeholder emits an artifact");
    assert!(matches!(
        artifact.run_i64(),
        Err(VmArtifactError::HostCallRequiresAuthority { capability, symbol })
            if capability == "process_args" && symbol == "__g1_process_args_get"
    ));
}

#[test]
fn manifest_host_placeholder_requires_its_declared_capability() {
    let mut input = request(
        "fn __g1_process_args_get() -> Array<Text> { () } pub fn main() -> Array<Text> { __g1_process_args_get() }",
    );
    input.runtime_manifest = Some(RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        selectors: vec![],
        host_imports: vec![HostImportSelector {
            module_path: "crate".into(),
            name: "__g1_process_args_get".into(),
            capability: "process_args".into(),
            symbol: "__g1_process_args_get".into(),
        }],
    });

    let error = StageZeroCompiler::new().compile(input).unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G7032"),
        "{error:#?}"
    );
}

#[test]
fn service_lowers_only_the_manifest_bound_abort_leaf_to_a_terminal_vm_trap() {
    let mut input = request("fn __g1_abort() -> ! { () } pub fn main() -> ! { __g1_abort() }");
    input.runtime_manifest = Some(RuntimeManifestInput {
        standard_library: PackageKey("app@0.1.0".into()),
        host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::Abort,
            module_path: "crate".into(),
            name: "__g1_abort".into(),
        }],
    });
    let outcome = StageZeroCompiler::new().compile(input).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{outcome:#?}");
    let artifact = outcome.artifact.expect("abort program emits an artifact");
    assert!(matches!(artifact.run_i64(), Err(VmArtifactError::Trap)));
}

#[test]
fn service_rejects_host_imports_escaping_as_ordinary_callable_values() {
    let mut input =
        request("host clock fn now() -> i64; pub fn main() -> i64 { let f = now; f() }");
    input.capability_manifest.push("clock".into());
    let error = StageZeroCompiler::new().compile(input).unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G6012"
                && diagnostic
                    .message
                    .contains("host imports may only be invoked")),
        "{error:#?}"
    );
}

#[test]
fn service_resolves_public_module_aliases_inside_qualified_body_paths() {
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(
            "pub mod api; pub mod facade; pub fn main() -> i64 { facade::client::answer() }",
            &[
                ("api", "pub fn answer() -> i64 { 42 }"),
                ("facade", "pub use crate::api as client;"),
            ],
        ))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_multihop_public_module_reexports_inside_qualified_paths() {
    let outcome = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            "pub mod api; pub mod facade; pub mod outer; pub fn main() -> i64 { outer::public_facade::client::nested::answer() }",
            &[
                ("src/api/api.glorious", "pub mod nested;"),
                ("src/api/nested/nested.glorious", "pub fn answer() -> i64 { 42 }"),
                ("src/facade/facade.glorious", "pub use crate::api as client;"),
                ("src/outer/outer.glorious", "pub use crate::facade as public_facade;"),
            ],
        ))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_keeps_private_module_aliases_lexical_to_their_declaring_module() {
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(
            "pub mod api; pub mod facade; pub fn main() -> i64 { facade::call() }",
            &[
                ("api", "pub fn answer() -> i64 { 42 }"),
                (
                    "facade",
                    "use crate::api as client; pub fn call() -> i64 { client::answer() }",
                ),
            ],
        ))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_missing_public_reexports_before_body_elaboration() {
    let error = StageZeroCompiler::new()
        .compile(request_with_modules(
            "pub mod facade; pub fn main() -> i64 { 42 }",
            &[("facade", "pub use crate::missing::answer;")],
        ))
        .unwrap_err();

    assert!(
        error.diagnostics().iter().any(|diagnostic| {
            diagnostic.code == "G3317" && diagnostic.message.contains("missing target")
        }),
        "{:#?}",
        error.diagnostics()
    );
}

#[test]
fn service_applies_host_instance_discovery_limits_before_lowering() {
    let compiler = StageZeroCompiler::with_instance_limits(InstanceLimits {
        total: 1,
        per_definition: 1,
        ..InstanceLimits::default()
    });
    let error = compiler
        .compile(request(
            "pub fn helper() -> i64 { 41 } pub fn main() -> i64 { helper() + 1 }",
        ))
        .unwrap_err();

    let diagnostics = error.diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "G7031"
            && diagnostic.class == DiagnosticClass::Resource
            && diagnostic.message.contains("TotalLimit { limit: 1")
    }));
}

#[test]
fn service_discovers_concrete_generic_direct_call_instances() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity(42) }",
        ))
        .unwrap();
    let instances = outcome
        .instance_graph
        .expect("instance discovery evidence")
        .ordered();
    assert_eq!(instances.len(), 2, "{instances:#?}");
    assert!(
        instances
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
}

#[test]
fn service_rejects_deep_concrete_instance_substitutions_before_lowering() {
    let compiler = StageZeroCompiler::with_instance_limits(InstanceLimits {
        substitution_depth: 1,
        ..InstanceLimits::default()
    });
    let error = compiler
        .compile(request(
            "pub struct Box<T> { value: T } pub fn identity<T>(value: T) -> T { value } pub fn main() -> Box<i64> { identity(Box { value: 42 }) }",
        ))
        .unwrap_err();

    assert!(error.diagnostics().iter().any(|diagnostic| {
        diagnostic.code == "G7031"
            && diagnostic.class == DiagnosticClass::Resource
            && diagnostic
                .message
                .contains("SubstitutionDepth { depth: 2, limit: 1")
    }));
}

#[test]
fn service_executes_a_concrete_generic_mir_instance_through_vm_linking() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity(42) }",
        ))
        .unwrap();
    let artifact = outcome.artifact.expect("build must publish a VM program");
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert!(
        outcome
            .instance_graph
            .expect("instance graph")
            .ordered()
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
}

#[test]
fn service_specializes_generic_aggregate_layout_metadata_before_vm_linking() {
    let source = "pub struct Box<T> { value: T } pub fn wrap<T>(value: T) -> Box<T> { Box<T> { value: value } } pub fn main() -> i64 { let boxed = wrap(42); boxed.value }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_finalizes_main_as_a_closed_zero_argument_effect_boundary() {
    for (source, message) in [
        (
            "pub fn main(value: i64) -> i64 { value }",
            "executable entry `main` must not declare parameters",
        ),
        (
            "pub fn main<T>() -> i64 { 0 }",
            "executable entry `main` cannot declare generic binders",
        ),
        (
            "pub fn main<e: EffectRow>() -> i64 / {| e} { 0 }",
            "executable entry `main` cannot declare generic binders",
        ),
        (
            "effect Trace { note(); } pub fn main() -> i64 / {Trace} { 0 }",
            "executable entry `main` must have a closed empty outward effect row",
        ),
    ] {
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
            StageZeroCompiler::new().compile(request(source))
        else {
            panic!("invalid executable entry unexpectedly compiled: {source}");
        };
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.code == "G7028" && diagnostic.message == message }),
            "missing executable-boundary diagnostic for {source}: {diagnostics:#?}"
        );
    }
}

#[test]
fn service_compiles_explicit_parent_and_child_revisions_without_world_mixing() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(request("pub fn main() -> i64 { 40 + 2 }"), None)
        .unwrap();
    let parent_outcome = compiler.compile_revision(parent).unwrap();
    assert_eq!(parent_outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let child = compiler
        .import_revision(request("pub fn main() -> i64 { 40 + 3 }"), Some(parent))
        .unwrap();
    let child_outcome = compiler.compile_revision(child).unwrap();
    assert_eq!(child_outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_tracks_private_body_edits_without_invalidating_public_products() {
    let compiler = StageZeroCompiler::new();
    let parent_request = request("pub fn helper() -> i64 { 1 } pub fn main() -> i64 { helper() }");
    let parent = compiler.import_revision(parent_request, None).unwrap();
    compiler.compile_revision(parent).unwrap();
    let child_request = request("pub fn helper() -> i64 { 2 } pub fn main() -> i64 { helper() }");
    let changed_file = child_request.sources[0].key;
    let child = compiler
        .import_revision(child_request, Some(parent))
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(child)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        2
    );

    let crate_module = ModuleKey {
        package: PackageKey("app@0.1.0".into()),
        path: "crate".into(),
    };
    assert!(matches!(
        compiler
            .dependency_trace(child, &DependencyNode::Input(changed_file))
            .unwrap()
            .status,
        DependencyStatus::Red { .. }
    ));
    assert!(matches!(
        compiler
            .dependency_trace(child, &DependencyNode::Interface(crate_module.clone()))
            .unwrap()
            .status,
        DependencyStatus::Green { parent: green_parent } if green_parent == parent
    ));
    assert!(matches!(
        compiler
            .dependency_trace(child, &DependencyNode::Fixity(crate_module))
            .unwrap()
            .status,
        DependencyStatus::Green { .. }
    ));
    let traces = compiler.dependency_traces(child);
    assert!(
        traces
            .iter()
            .any(|trace| matches!(trace.node, DependencyNode::Core(_))
                && matches!(trace.status, DependencyStatus::Red { .. }))
    );
    assert!(matches!(
        traces
            .iter()
            .find(|trace| matches!(trace.node, DependencyNode::Artifact(_)))
            .unwrap()
            .status,
        DependencyStatus::Red { ref first_changed, .. } if *first_changed == DependencyNode::Input(changed_file)
    ));
}

#[test]
fn service_invalidates_public_glob_facades_when_the_target_api_changes() {
    let compiler = StageZeroCompiler::new();
    let root = "pub mod api; pub mod facade; pub fn main() -> i64 { 42 }";
    let parent = compiler
        .import_revision(
            request_with_logical_sources(
                root,
                &[
                    ("src/api/api.glorious", "pub fn answer() -> i64 { 1 }"),
                    ("src/facade/facade.glorious", "pub use crate::api::*;"),
                ],
            ),
            None,
        )
        .unwrap();
    compiler.compile_revision(parent).unwrap();
    let child = compiler
        .import_revision(
            request_with_logical_sources(
                root,
                &[
                    (
                        "src/api/api.glorious",
                        "pub fn answer() -> i64 { 1 } pub fn later() -> i64 { 2 }",
                    ),
                    ("src/facade/facade.glorious", "pub use crate::api::*;"),
                ],
            ),
            Some(parent),
        )
        .unwrap();
    compiler.compile_revision(child).unwrap();

    let package = PackageKey("app@0.1.0".into());
    for path in ["crate", "crate::facade"] {
        let module = ModuleKey {
            package: package.clone(),
            path: path.into(),
        };
        assert!(matches!(
            compiler
                .dependency_trace(child, &DependencyNode::Interface(module))
                .unwrap()
                .status,
            DependencyStatus::Red { .. }
        ));
    }
}

#[test]
fn service_keeps_public_glob_facades_green_for_private_target_edits() {
    let compiler = StageZeroCompiler::new();
    let root = "pub mod api; pub mod facade; pub fn main() -> i64 { 42 }";
    let parent = compiler
        .import_revision(
            request_with_logical_sources(
                root,
                &[
                    (
                        "src/api/api.glorious",
                        "pub fn answer() -> i64 { 1 } fn hidden() -> i64 { 1 }",
                    ),
                    ("src/facade/facade.glorious", "pub use crate::api::*;"),
                ],
            ),
            None,
        )
        .unwrap();
    compiler.compile_revision(parent).unwrap();
    let child = compiler
        .import_revision(
            request_with_logical_sources(
                root,
                &[
                    (
                        "src/api/api.glorious",
                        "pub fn answer() -> i64 { 1 } fn hidden() -> i64 { 2 }",
                    ),
                    ("src/facade/facade.glorious", "pub use crate::api::*;"),
                ],
            ),
            Some(parent),
        )
        .unwrap();
    compiler.compile_revision(child).unwrap();

    let package = PackageKey("app@0.1.0".into());
    let api_interface = DependencyNode::Interface(ModuleKey {
        package: package.clone(),
        path: "crate::api".into(),
    });
    for path in ["crate", "crate::api", "crate::facade"] {
        let module = ModuleKey {
            package: package.clone(),
            path: path.into(),
        };
        assert!(matches!(
            compiler
                .dependency_trace(child, &DependencyNode::Interface(module))
                .unwrap()
                .status,
            DependencyStatus::Green { parent: green_parent } if green_parent == parent
        ));
    }
    let facade = compiler
        .dependency_trace(
            child,
            &DependencyNode::Interface(ModuleKey {
                package,
                path: "crate::facade".into(),
            }),
        )
        .unwrap();
    assert!(
        facade.dependencies.contains(&api_interface),
        "the public glob facade records the target interface even when that target stays green"
    );
}

#[test]
fn service_invalidates_explicit_and_module_reexports_with_their_target_contract() {
    let compiler = StageZeroCompiler::new();
    let root = "pub mod api; pub mod explicit; pub mod module; pub fn main() -> i64 { 42 }";
    let parent = compiler
        .import_revision(
            request_with_logical_sources(
                root,
                &[
                    ("src/api/api.glorious", "pub fn answer() -> i64 { 1 }"),
                    (
                        "src/explicit/explicit.glorious",
                        "pub use crate::api::answer;",
                    ),
                    (
                        "src/module/module.glorious",
                        "pub use crate::api as client;",
                    ),
                ],
            ),
            None,
        )
        .unwrap();
    compiler.compile_revision(parent).unwrap();
    let child = compiler
        .import_revision(
            request_with_logical_sources(
                root,
                &[
                    (
                        "src/api/api.glorious",
                        "pub fn answer(value: i64) -> i64 { value }",
                    ),
                    (
                        "src/explicit/explicit.glorious",
                        "pub use crate::api::answer;",
                    ),
                    (
                        "src/module/module.glorious",
                        "pub use crate::api as client;",
                    ),
                ],
            ),
            Some(parent),
        )
        .unwrap();
    compiler.compile_revision(child).unwrap();

    let package = PackageKey("app@0.1.0".into());
    let api_interface = DependencyNode::Interface(ModuleKey {
        package: package.clone(),
        path: "crate::api".into(),
    });
    let api_input = DependencyNode::Input(FileKey::new(&package, "src/api/api.glorious"));
    for path in ["crate", "crate::explicit", "crate::module"] {
        let module = ModuleKey {
            package: package.clone(),
            path: path.into(),
        };
        let trace = compiler
            .dependency_trace(child, &DependencyNode::Interface(module))
            .unwrap();
        assert!(
            trace.dependencies.contains(&api_interface),
            "{path} must retain the public API interface it exposes"
        );
        assert!(matches!(
            trace.status,
            DependencyStatus::Red { ref first_changed, .. } if *first_changed == api_input
        ));
    }
}

#[test]
fn service_traces_concrete_instances_and_invalidates_changed_callee_edges() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            request("pub fn helper() -> i64 { 1 } pub fn main() -> i64 { helper() }"),
            None,
        )
        .unwrap();
    let parent_outcome = compiler.compile_revision(parent).unwrap();
    let parent_graph = parent_outcome.instance_graph.expect("instance graph");
    assert_eq!(parent_graph.ordered().len(), 2);
    let main = parent_graph
        .roots()
        .keys()
        .next()
        .expect("entry instance")
        .clone();
    let helper = parent_graph
        .callees(&main)
        .unwrap()
        .iter()
        .next()
        .unwrap()
        .clone();
    assert!(matches!(
        compiler
            .dependency_trace(parent, &DependencyNode::Instance(main.clone()))
            .unwrap()
            .status,
        DependencyStatus::Cold
    ));
    let child = compiler
        .import_revision(
            request("pub fn helper() -> i64 { 2 } pub fn main() -> i64 { helper() }"),
            Some(parent),
        )
        .unwrap();
    compiler.compile_revision(child).unwrap();
    let trace = compiler
        .dependency_trace(child, &DependencyNode::Instance(helper))
        .unwrap();
    assert!(
        trace
            .dependencies
            .iter()
            .any(|dependency| matches!(dependency, DependencyNode::Body(_)))
    );
}

#[test]
fn service_tracks_public_interface_edits_without_invalidating_unaffected_bodies() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            request("pub struct Version { value: i64 } pub fn main() -> i64 { 42 }"),
            None,
        )
        .unwrap();
    compiler.compile_revision(parent).unwrap();
    let child = compiler
        .import_revision(
            request("pub struct Version { value: i64, next: i64 } pub fn main() -> i64 { 42 }"),
            Some(parent),
        )
        .unwrap();
    compiler.compile_revision(child).unwrap();
    let traces = compiler.dependency_traces(child);
    assert!(matches!(
        compiler
            .dependency_trace(
                child,
                &DependencyNode::Interface(ModuleKey {
                    package: PackageKey("app@0.1.0".into()),
                    path: "crate".into(),
                }),
            )
            .unwrap()
            .status,
        DependencyStatus::Red { .. }
    ));
    // The body was revalidated against the new interface but its frozen Core
    // is equal, so no downstream work need treat it as red.
    assert!(
        traces
            .iter()
            .any(|trace| matches!(trace.node, DependencyNode::Core(_))
                && matches!(trace.status, DependencyStatus::Green { .. }))
    );
}

#[test]
fn service_sessions_pin_retired_revisions_without_mixing_live_worlds() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(request("pub fn main() -> i64 { 40 + 2 }"), None)
        .unwrap();
    let child = compiler
        .import_revision(request("pub fn main() -> i64 { 40 + 3 }"), Some(parent))
        .unwrap();
    let parent_session = compiler.open_session(parent).unwrap();
    let child_session = compiler.open_session(child).unwrap();
    assert_eq!(parent_session.metadata().parent, None);
    assert_eq!(child_session.metadata().parent, Some(parent));
    assert_ne!(
        parent_session.metadata().input_fingerprint,
        child_session.metadata().input_fingerprint
    );

    compiler.retire_revision(parent).unwrap();
    assert!(matches!(
        compiler.open_session(parent),
        Err(error) if error.diagnostics()[0].code == "G7027"
    ));
    assert_eq!(
        compiler.collect_retired(),
        RetentionReport {
            collected: 0,
            retained_pinned: 1,
        }
    );

    // Retirement cannot redirect either already-admitted request to a newer
    // source world. The pinned parent remains executable while the child
    // observes its own independent revision.
    assert_eq!(
        compiler
            .compile_session(&parent_session)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    assert_eq!(
        compiler
            .compile_session(&child_session)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        43
    );
    assert!(matches!(
        StageZeroCompiler::new().compile_session(&child_session),
        Err(error) if error.diagnostics()[0].code == "G7026"
    ));
    assert!(matches!(
        compiler.compile_session(&child_session),
        Err(error) if error.diagnostics()[0].code == "G7034"
    ));

    drop(parent_session);
    assert_eq!(
        compiler.collect_retired(),
        RetentionReport {
            collected: 1,
            retained_pinned: 0,
        }
    );
    assert!(matches!(
        compiler.open_session(parent),
        Err(error) if error.diagnostics()[0].code == "G7025"
    ));
    let resumed_child_session = compiler.open_session(child).unwrap();
    assert_eq!(
        compiler
            .compile_session(&resumed_child_session)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        43
    );
}

#[test]
fn retired_query_cache_reclamation_preserves_new_revision_runtime() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(request("pub fn main() -> i64 { 42 }"), None)
        .unwrap();
    let child = compiler
        .import_revision(request("pub fn main() -> i64 { 43 }"), Some(parent))
        .unwrap();
    let engine = Arc::new(QueryEngine::new(SourceWorldFingerprint));
    compiler.register_revision_cache(&engine);
    let session = compiler.open_session(parent).unwrap();
    let cancellation = CancellationToken::new();
    let budget = Budget::root("service-query-retention", 2);
    let parent_fingerprint = engine
        .execute(session.snapshot(), (), &cancellation, &budget)
        .unwrap()
        .value;
    assert_eq!(parent_fingerprint, session.metadata().input_fingerprint);
    assert_eq!(engine.memo().retained_entry_count(), 1);

    // The old world can still compile and execute while its request owns a
    // snapshot pin, even though no new request may enter it.
    compiler.retire_revision(parent).unwrap();
    assert_eq!(
        compiler
            .compile_session(&session)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    assert_eq!(compiler.collect_retired().retained_pinned, 1);
    assert_eq!(engine.memo().retained_entry_count(), 1);

    drop(session);
    assert_eq!(compiler.collect_retired().collected, 1);
    assert_eq!(engine.memo().retained_entry_count(), 0);
    assert_eq!(engine.retained_execution_count(), 0);

    // The child is a distinct source world. Its VM artifact remains correct
    // after the old query provenance and value state have been reclaimed.
    assert_eq!(
        compiler
            .compile_revision(child)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        43
    );
}

#[test]
fn cancelled_service_sessions_discard_staged_cache_artifacts_and_release_pins() {
    let compiler = StageZeroCompiler::new();
    let revision = compiler
        .import_revision(
            request_with_module(
                "mod math; pub fn main() -> i64 { math::answer() }",
                "pub fn answer() -> i64 { 42 }",
            ),
            None,
        )
        .unwrap();
    let cancellation = CancellationToken::new();
    let budget = Budget::root("request", 4);
    let session = compiler
        .open_session_with_controls(revision, cancellation.clone(), budget.clone())
        .unwrap();
    cancellation.cancel();

    let error = compiler.compile_session(&session).unwrap_err();
    assert_eq!(error.diagnostics()[0].code, "G7029");
    // `compile_session` returned no `CompilationOutcome`, so no artifact can
    // cross the request publication boundary.
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 0);
    assert!(compiler.dependency_traces(revision).is_empty());
    assert_eq!(budget.spent(), 0);
    assert!(matches!(
        compiler.compile_session(&session),
        Err(error) if error.diagnostics()[0].code == "G7034"
    ));
    assert!(
        compiler.dependency_traces(revision).is_empty(),
        "a cancelled session cannot be replayed into a later publication"
    );

    compiler.retire_revision(revision).unwrap();
    assert_eq!(compiler.collect_retired().retained_pinned, 1);
    drop(session);
    assert_eq!(compiler.collect_retired().collected, 1);
}

#[test]
fn failed_and_resource_limited_sessions_do_not_publish_staged_interfaces() {
    let compiler = StageZeroCompiler::new();
    let failed_revision = compiler
        .import_revision(
            request_with_module(
                "mod math; pub fn helper() -> i64 { math::answer() }",
                "pub fn answer() -> i64 { 42 }",
            ),
            None,
        )
        .unwrap();
    let failed_session = compiler.open_session(failed_revision).unwrap();
    assert!(compiler.compile_session(&failed_session).is_err());
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 0);
    assert!(compiler.dependency_traces(failed_revision).is_empty());

    let limited_revision = compiler
        .import_revision(request("pub fn main() -> i64 { 42 }"), None)
        .unwrap();
    let budget = Budget::root("request", 0);
    let limited_session = compiler
        .open_session_with_controls(limited_revision, CancellationToken::new(), budget.clone())
        .unwrap();
    let error = compiler.compile_session(&limited_session).unwrap_err();
    assert_eq!(error.diagnostics()[0].code, "G7030");
    assert_eq!(budget.spent(), 0);
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 0);
    assert!(compiler.dependency_traces(limited_revision).is_empty());
}

#[test]
fn service_request_package_registry_commits_or_rolls_back_atomically() {
    let compiler = StageZeroCompiler::new();
    let good_revision = compiler
        .import_revision(request("pub fn main() -> i64 { 42 }"), None)
        .unwrap();
    let good = compiler.open_session(good_revision).unwrap();
    assert!(good.package_sessions().is_empty());
    assert_eq!(good.retention_metadata().active_packages, 0);
    assert_eq!(good.retention_metadata().active_body_scratch, 0);
    assert_eq!(good.retention_metadata().staged_body_products, 0);
    compiler.compile_session(&good).unwrap();
    assert_eq!(
        good.package_sessions()
            .iter()
            .map(|entry| entry.status)
            .collect::<Vec<_>>(),
        vec![PackageSessionStatus::Committed]
    );
    let committed = good.retention_metadata();
    assert_eq!(committed.active_packages, 0);
    assert_eq!(committed.active_body_scratch, 0);
    assert_eq!(committed.staged_body_products, 0);
    assert!(
        committed
            .packages
            .iter()
            .all(|package| package.active_body_scratch == 0 && package.staged_body_products == 0)
    );

    // A failure after body-session admission must abandon every request-local
    // package product rather than leaving a partially staged package that a
    // later request could mistake for a completed interface/body/MIR result.
    let failed_revision = compiler
        .import_revision(request("pub fn main() -> i64 { missing_name }"), None)
        .unwrap();
    let failed = compiler.open_session(failed_revision).unwrap();
    assert!(compiler.compile_session(&failed).is_err());
    assert_eq!(
        failed
            .package_sessions()
            .iter()
            .map(|entry| entry.status)
            .collect::<Vec<_>>(),
        vec![PackageSessionStatus::RolledBack]
    );
    let rolled_back = failed.retention_metadata();
    assert_eq!(rolled_back.active_packages, 0);
    assert_eq!(rolled_back.active_body_scratch, 0);
    assert_eq!(rolled_back.staged_body_products, 0);
    assert!(
        rolled_back
            .packages
            .iter()
            .all(|package| package.active_body_scratch == 0 && package.staged_body_products == 0)
    );
}

#[test]
fn failed_dependency_package_resolution_discards_all_staged_package_interfaces() {
    let compiler = StageZeroCompiler::new();
    let revision = compiler
        .import_revision(
            request_with_dependency(
                "use math::secret; pub fn main() -> i64 { secret() }",
                "math@0.1.0",
                "fn secret() -> i64 { 42 }",
            ),
            None,
        )
        .unwrap();
    let session = compiler.open_session(revision).unwrap();
    assert!(compiler.compile_session(&session).is_err());
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 0);
    assert!(
        compiler.dependency_traces(revision).is_empty(),
        "a failed dependency interface must not partially publish root or dependency facts"
    );
}

#[test]
fn request_work_budget_bounds_declaration_heavy_compilation_before_publication() {
    let compiler = StageZeroCompiler::new();
    let mut source = String::new();
    for index in 0..32 {
        source.push_str(&format!("pub fn helper_{index}() -> i64 {{ {index} }} "));
    }
    source.push_str("pub fn main() -> i64 { helper_31() }");
    let revision = compiler.import_revision(request(&source), None).unwrap();
    // Admission, source/module traversal, and a few declarations fit; the
    // remaining hostile declaration stream must consume the same request
    // budget rather than slipping through zero-cost checkpoints.
    let budget = Budget::root("request-work", 12);
    let session = compiler
        .open_session_with_controls(revision, CancellationToken::new(), budget.clone())
        .unwrap();
    let error = compiler.compile_session(&session).unwrap_err();
    assert_eq!(error.diagnostics()[0].code, "G7030");
    assert_eq!(budget.spent(), 12, "resource work must be cumulative");
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 0);
    assert!(
        compiler.dependency_traces(revision).is_empty(),
        "an exhausted request must discard staged dependency facts"
    );
}

#[test]
fn service_reuses_only_unchanged_frozen_module_interfaces_across_revisions() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            request_with_module(
                "mod math; pub fn main() -> i64 { math::answer() + 1 }",
                "pub fn answer() -> i64 { 41 }",
            ),
            None,
        )
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(parent)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 2);

    // Replacing only the root source must recollect that interface while the
    // unchanged external module is validated and reused in the child world.
    let root_changed = compiler
        .import_revision(
            request_with_module(
                "mod math; pub fn main() -> i64 { math::answer() + 2 }",
                "pub fn answer() -> i64 { 41 }",
            ),
            Some(parent),
        )
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(root_changed)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        43
    );
    assert_eq!(
        compiler.interface_cache_stats(),
        grandiose_stage0::InterfaceCacheStats { hits: 1, misses: 3 }
    );

    // The next child changes the dependency interface itself. The root can
    // reuse its exact frozen interface, but `math` must be recollected and the
    // new executable result proves no old interface/body product leaked.
    let dependency_changed = compiler
        .import_revision(
            request_with_module(
                "mod math; pub fn main() -> i64 { math::answer() + 2 }",
                "pub fn answer() -> i64 { 42 }",
            ),
            Some(root_changed),
        )
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(dependency_changed)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        44
    );
    assert_eq!(
        compiler.interface_cache_stats(),
        grandiose_stage0::InterfaceCacheStats { hits: 2, misses: 4 }
    );
}

#[test]
fn service_lowers_word_boolean_operators_as_short_circuit_cfg() {
    let false_and = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { false and (1 / 0 == 0) }"))
        .unwrap();
    assert!(!false_and.artifact.unwrap().run_bool().unwrap());

    let true_or = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { true or (1 / 0 == 0) }"))
        .unwrap();
    assert!(true_or.artifact.unwrap().run_bool().unwrap());
}

#[test]
fn service_exposes_canonical_verified_vm_program_bytes_for_external_tools() {
    let artifact = StageZeroCompiler::new()
        .compile(request(
            "pub fn helper() -> i64 { 40 } pub fn main() -> i64 { helper() + 2 }",
        ))
        .unwrap()
        .artifact
        .unwrap();
    let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    assert_eq!(decoded.fingerprint(), artifact.fingerprint());
    assert_eq!(decoded.run_i64().unwrap(), 42);
}

#[test]
fn service_renders_any_verified_vm_entry_value_for_host_tools() {
    let tuple = StageZeroCompiler::new()
        .compile(request("pub fn main() -> (i64, i64) { (40, 2) }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(tuple.run_display().unwrap(), "(40, 2)");

    let text = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Text { \"glorious\" }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(text.run_display().unwrap(), "\"glorious\"");
}

#[test]
fn service_lowers_addressable_local_assignment_through_placeflow_and_the_vm() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let value = 1; value = 42; value }",
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_assignment_inside_a_lifted_closure_with_its_own_storage_graph() {
    let source = r#"
        pub fn main() -> i64 {
            let seed = 0;
            let delayed = (input: i64) -> i64 {
                let value = input;
                value = seed + 1;
                value
            };
            delayed(0)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 1);
}

#[test]
fn service_lowers_unique_borrow_deref_and_mutation_without_copying_the_place() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let value = 1; let reference = &mut value; *reference = 42; *reference }",
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_unique_reference_writeback_across_a_direct_call_and_return() {
    let source = "pub fn overwrite<'a>(value: &'a mut i64) -> &'a mut i64 { *value = 42; value } pub fn main() -> i64 { let value = 1; let returned = overwrite(&mut value); *returned = 43; value }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn affine_nominal_values_cannot_copy_an_embedded_unique_reference() {
    let source = r#"
        pub struct Holder { reference: &mut i64 }
        pub fn main() -> i64 {
            let value = 1;
            let parent = &mut value;
            let holder = Holder { reference: move parent };
            let alias = holder;
            *alias.reference = 42;
            *holder.reference
        }
    "#;
    assert!(
        StageZeroCompiler::new().compile(request(source)).is_err(),
        "copying a nominal carrier must not duplicate its unique reference"
    );
}

#[test]
fn shared_dereference_cannot_be_used_as_a_mutation_place() {
    let diagnostics = match StageZeroCompiler::new().compile(request(
        "pub fn main() -> i64 { let value = 1; let reference = &value; *reference = 42; value }",
    )) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("shared-reference mutation unexpectedly compiled: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4141")
    );
}

#[test]
fn reference_to_body_local_cannot_escape_as_a_return_value() {
    let diagnostics = match StageZeroCompiler::new()
        .compile(request("pub fn main() -> &i64 { let value = 1; &value }"))
    {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("body-local reference unexpectedly escaped: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "missing body-local reference escape diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn body_local_reference_cannot_be_stored_through_a_caller_owned_reference() {
    let diagnostics = match StageZeroCompiler::new().compile(request(
        "pub fn bad(slot: &mut &i64) -> i64 { let value = 1; *slot = &value; 0 } pub fn main() -> i64 { 0 }",
    )) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("body-local reference unexpectedly escaped through caller storage: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5022"),
        "missing external-store drop-check diagnostic: {diagnostics:#?}"
    );

    let nested_diagnostics = match StageZeroCompiler::new().compile(request(
        "pub struct Holder { reference: &i64 } pub fn bad(slot: &mut Holder) -> i64 { let value = 1; (*slot).reference = &value; 0 } pub fn main() -> i64 { 0 }",
    )) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("body-local reference unexpectedly escaped through caller aggregate storage: {outcome:#?}"),
    };
    assert!(
        nested_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5022"),
        "missing nested external-store drop-check diagnostic: {nested_diagnostics:#?}"
    );

    let closure_diagnostics = match StageZeroCompiler::new().compile(request(
        "pub fn bad(slot: &mut (() -> i64)) -> i64 { let value = 1; let loan = &value; *slot = () -> i64 { *loan }; 0 } pub fn main() -> i64 { 0 }",
    )) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("body-local closure unexpectedly escaped through caller storage: {outcome:#?}"),
    };
    assert!(
        closure_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5022"),
        "missing closure external-store drop-check diagnostic: {closure_diagnostics:#?}"
    );

    let cancelled_handler_diagnostics = match StageZeroCompiler::new().compile(request(
        "effect Ask { [0, 1] ask() -> i64; } pub fn bad(slot: &mut &i64) -> i64 / {Ask} { let value = 1; handle Ask::ask() { Ask::ask() with _ => { *slot = &value; 0 } } } pub fn main() -> i64 { 0 }",
    )) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("handler cancellation unexpectedly stored a body-local reference externally: {outcome:#?}"),
    };
    assert!(
        cancelled_handler_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5022"),
        "missing cancellation external-store drop-check diagnostic: {cancelled_handler_diagnostics:#?}"
    );

    let local_slot = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let first = 1; let second = 42; let reference = &first; let slot = &mut reference; *slot = &second; *reference }",
        ))
        .expect("a local reference slot is destroyed with its referents");
    assert!(
        local_slot.diagnostics.is_empty(),
        "{:#?}",
        local_slot.diagnostics
    );
    assert_eq!(
        local_slot.artifact.unwrap().run_i64().unwrap(),
        42,
        "borrowing `reference` must preserve the carrier slot as `&mut &i64`, not reborrow its i64 referent"
    );

    let external_value = StageZeroCompiler::new()
        .compile(request(
            "pub fn relay(slot: &mut &i64, value: &i64) -> i64 { *slot = value; 0 } pub fn main() -> i64 { 0 }",
        ))
        .expect("caller-owned storage may retain a reference supplied by the caller");
    assert!(
        external_value.diagnostics.is_empty(),
        "{:#?}",
        external_value.diagnostics
    );
}

#[test]
fn active_unique_loan_rejects_move_of_its_referent() {
    let diagnostics = match StageZeroCompiler::new().compile(request(
        "pub fn main() -> i64 { let value = 1; let reference = &mut value; move value; *reference }",
    )) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("move while uniquely borrowed unexpectedly compiled: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004"),
        "missing move-while-borrowed diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn unique_field_borrow_preserves_the_projected_place_identity() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let reference = &mut pair.left; *reference = 42; pair.left }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn unique_reborrow_reuses_the_original_vm_place() {
    let source = "pub fn main() -> i64 { let value = 1; let parent = &mut value; let child = &mut *parent; *child = 42; *parent }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn whole_unique_referent_move_requires_exact_restoration_before_reuse() {
    let restored = "pub fn relay(value: i64) -> i64 { value } pub fn main() -> i64 { let value = 1; let reference = &mut value; let moved = move *reference; let retained = relay(moved); *reference = retained + 41; *reference }";
    let outcome = StageZeroCompiler::new()
        .compile(request(restored))
        .expect("a whole unique referent may be moved and exactly restored");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let read_before_restore = "pub fn main() -> i64 { let value = 1; let reference = &mut value; let moved = move *reference; *reference + moved }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(read_before_restore))
    else {
        panic!("a unique-reference referent hole unexpectedly permitted a read");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001" || diagnostic.code == "G5004"),
        "missing use-through-open-referent diagnostic: {diagnostics:#?}"
    );

    let incomplete = "pub fn main() -> i64 { let value = 1; let reference = &mut value; let moved = move *reference; moved }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(incomplete))
    else {
        panic!("a body unexpectedly completed with an open unique-reference referent hole");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G5004"),
        "missing open-referent scope-exit diagnostic: {diagnostics:#?}"
    );

    let alias = "pub fn main() -> i64 { let value = 1; let reference = &mut value; let moved = move *reference; let alias = reference; *alias = moved; *alias }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(alias))
    else {
        panic!("an alias unexpectedly observed an open unique-reference referent hole");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G5004"),
        "missing alias-through-open-referent diagnostic: {diagnostics:#?}"
    );

    let nested_scope = "pub fn main() -> i64 { { let value = 1; let reference = &mut value; let moved = move *reference; moved }; 0 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(nested_scope))
    else {
        panic!("a nested scope unexpectedly ended with an open unique-reference referent hole");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G5004"),
        "missing nested scope referent-hole diagnostic: {diagnostics:#?}"
    );

    let shared = "pub fn main() -> i64 { let value = 1; let reference = &value; move *reference }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(shared))
    else {
        panic!("a shared-reference referent unexpectedly moved out");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G5004"),
        "missing shared-referent move diagnostic: {diagnostics:#?}"
    );

    let handler_boundary = "effect Tick { [0,1] tick() -> i64; } pub fn main() -> i64 { let value = 1; let reference = &mut value; let moved = move *reference; handle Tick::tick() { Tick::tick() with _ => moved } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(handler_boundary))
    else {
        panic!("a handler unexpectedly captured an open unique-reference referent hole");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G5004"),
        "missing handler-boundary referent-hole diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn nested_projection_reborrows_preserve_origin_and_reject_suspension_escape() {
    let source = r#"
        pub struct Inner { value: i64 }
        pub struct Outer { inner: Inner, tag: i64 }
        pub fn main() -> i64 {
            let outer = Outer { inner: Inner { value: 42 }, tag: 0 };
            let parent = &mut outer.inner.value;
            let child = &mut *parent;
            *child
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let escaping = r#"
        effect Store { save(value: &mut i64); }
        pub struct Inner { value: i64 }
        pub struct Outer { inner: Inner, tag: i64 }
        pub fn bad() -> i64 / {Store} {
            let outer = Outer { inner: Inner { value: 1 }, tag: 0 };
            let parent = &mut outer.inner.value;
            let child = &mut *parent;
            Store::save(child);
            0
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(escaping))
    else {
        panic!("nested reborrow escaped through an effect payload")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5015"),
        "missing nested-reborrow suspension diagnostic: {diagnostics:#?}"
    );

    let aggregate_held = r#"
        pub struct Holder { reference: &mut i64 }
        pub struct Outer { holder: Holder }
        pub fn main() -> i64 {
            let value = 1;
            let outer = Outer { holder: Holder { reference: &mut value } };
            let child = &mut *outer.holder.reference;
            *child
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(aggregate_held))
        .expect("aggregate-held reborrow must retain its backing loan origin");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 1);

    let replacement = r#"
        pub struct Holder { reference: &mut i64 }
        pub fn main() -> i64 {
            let first = 1;
            let second = 2;
            let holder = Holder { reference: &mut first };
            holder.reference = &mut second;
            let child = &mut *holder.reference;
            *child
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(replacement))
        .expect("reassigned aggregate reference must replace its origin");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 2);
}

#[test]
fn reborrow_suspends_its_aggregate_reference_carrier_until_nll_release() {
    let replacement_while_live = r#"
        pub struct Holder { loan: &mut i64, tag: i64 }
        pub fn main() -> i64 {
            let first = 1;
            let second = 2;
            let holder = Holder { loan: &mut first, tag: 0 };
            let child = &mut *holder.loan;
            holder.loan = &mut second;
            *child
        }
    "#;
    let diagnostics = match StageZeroCompiler::new().compile(request(replacement_while_live)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!(
            "replacement of a suspended aggregate reference carrier unexpectedly compiled: {outcome:#?}"
        ),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004"),
        "missing aggregate-carrier reborrow conflict: {diagnostics:#?}"
    );

    let replacement_after_last_use = r#"
        pub struct Holder { loan: &mut i64, tag: i64 }
        pub fn main() -> i64 {
            let first = 1;
            let second = 2;
            let holder = Holder { loan: &mut first, tag: 0 };
            let child = &mut *holder.loan;
            *child = 3;
            holder.loan = &mut second;
            *holder.loan
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(replacement_after_last_use))
        .expect("NLL must release a consumed child reborrow before carrier replacement");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 2);
}

#[test]
fn parent_unique_reference_is_suspended_while_a_unique_reborrow_is_live() {
    let source = "pub fn main() -> i64 { let value = 1; let parent = &mut value; let child = &mut *parent; *parent = 2; *child }";
    let diagnostics = match StageZeroCompiler::new().compile(request(source)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("active unique reborrow failed to suspend its parent: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004"),
        "missing parent-reborrow conflict: {diagnostics:#?}"
    );
}

#[test]
fn sibling_shared_reborrows_keep_the_parent_region_live() {
    let source = "pub fn main() -> i64 { let value = 21; let parent = &mut value; let left = & *parent; let right = & *parent; *left + *right }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn handler_join_retains_shared_reborrow_region_provenance() {
    let source = "effect Stop { stop() -> !; } pub fn main() -> i64 { let value = 21; let parent = &mut value; let child = & *parent; handle Stop::stop() { Stop::stop() => 0 }; *child + *child }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn handler_join_keeps_shared_reborrow_parent_suspended() {
    let source = "effect Stop { stop() -> !; } pub fn main() -> i64 { let value = 1; let parent = &mut value; let child = & *parent; handle Stop::stop() { Stop::stop() => 0 }; *parent = 2; *child }";
    let diagnostics = match StageZeroCompiler::new().compile(request(source)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("handler join reopened a suspended parent: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004")
    );
}

#[test]
fn nll_releases_a_handler_local_closure_capture_after_its_last_use() {
    let source = r#"
        effect Ask { [0, 1] ask() -> i64; }
        pub fn main() -> i64 {
            let value = 1;
            handle Ask::ask() {
                Ask::ask() with _ => {
                    let loan = &value;
                    let callback = () -> i64 { *loan };
                    callback();
                    0
                }
            };
            value = 42;
            value
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("a closure dead at the end of a handler arm must not retain its capture");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn nll_keeps_a_closure_capture_live_across_a_handler_when_used_afterward() {
    let source = r#"
        effect Ask { [0, 1] ask() -> i64; }
        pub fn main() -> i64 {
            let value = 1;
            let loan = &value;
            let callback = () -> i64 { *loan };
            handle Ask::ask() { Ask::ask() with _ => 0 };
            value = 42;
            callback()
        }
    "#;
    let diagnostics = match StageZeroCompiler::new().compile(request(source)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("a live closure capture unexpectedly allowed mutation: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5007"),
        "missing live closure-capture loan diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn nll_does_not_treat_the_dead_suffix_of_a_label_transfer_as_a_loan_use() {
    let source = r#"
        pub fn main() -> i64 {
            let value = 1;
            label done {
                let loan = &mut value;
                transfer done 0;
                *loan
            };
            value = 42;
            value
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("a transfer must not keep a dead suffix loan live");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn nll_distinguishes_a_shadowed_local_from_an_outer_live_loan() {
    let source = r#"
        pub fn main() -> i64 {
            let value = 1;
            let outer = &mut value;
            { let value = 2; value = 3; value };
            *outer = 42;
            *outer
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("an inner shadow must not alias the outer loan");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn nll_releases_a_reborrow_created_before_a_label_transfer() {
    let source = r#"
        pub fn main() -> i64 {
            let value = 1;
            let parent = &mut value;
            label done {
                let child = &mut *parent;
                transfer done 0;
                *child
            };
            *parent = 42;
            *parent
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("a transfer must clean its child reborrow before rejoining the label");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn shared_reborrow_still_suspends_unique_parent_mutation() {
    let source = "pub fn main() -> i64 { let value = 1; let parent = &mut value; let child = & *parent; *parent = 2; *child }";
    let diagnostics = match StageZeroCompiler::new().compile(request(source)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("shared reborrow failed to suspend parent mutation: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004")
    );
}

#[test]
fn assignment_reinitializes_a_local_after_a_whole_value_move() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let value = 1; move value; value = 42; value }",
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_disjoint_aggregate_fields_after_a_partial_move() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; move pair.left; pair.right }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 2);
}

#[test]
fn service_allows_partial_move_when_a_conditional_drop_impl_is_not_selected() {
    // A `Drop` implementation is selected trait evidence, not a nominal-name
    // property.  `Pair<i64>` has no `Mark` evidence, so its conditional hook
    // does not apply and its visible fields retain ordinary partial-move
    // semantics.
    let source = "trait Mark: Use<[0, 0]> {} pub struct Pair<T> { left: T, right: i64 } impl<T> Use<[0, 0]> for Pair<T> where T: Mark {} impl<T> Drop for Pair<T> where T: Mark { drop(&mut self) -> {} } pub fn main() -> i64 { let pair = Pair<i64> { left: 40, right: 2 }; move pair.left + pair.right }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_partial_move_when_a_conditional_drop_impl_is_selected() {
    // The matching instantiation remains opaque: selecting a conditional
    // hook must retain the same complete-aggregate guarantee as a direct
    // `Drop` implementation.
    let source = "trait Mark: Use<[0, 0]> {} pub struct Marker {} impl Use<[0, 0]> for Marker {} impl Mark for Marker {} pub struct Pair<T> { left: T, right: i64 } impl<T> Use<[0, 0]> for Pair<T> where T: Mark {} impl<T> Drop for Pair<T> where T: Mark { drop(&mut self) -> {} } pub fn main() -> i64 { let pair = Pair<Marker> { left: Marker {}, right: 2 }; move pair.left; pair.right }";
    let diagnostics = match StageZeroCompiler::new().compile(request(source)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("selected conditional Drop unexpectedly compiled: {outcome:#?}"),
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G4188"),
        "expected custom-Drop partial-move rejection, got {diagnostics:#?}"
    );
}

/// Exercise the ordinary service path for the source-level shape that reaches
/// a handler, a partial aggregate move, and a nonlocal lexical exit together.
/// The Core test inspects the intermediate frozen MIR; this companion proves
/// that the same shape is published, encoded, verified, and executed by a
/// normal compilation request.
#[test]
fn service_executes_handler_partial_move_and_label_leave() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64; }
        pub struct Pair { left: i64, right: i64 }
        pub fn main() -> i64 {
            label done {
                let pair = Pair { left: 1, right: 2 };
                move pair.left;
                handle Ask::ask() {
                    Ask::ask() => transfer done pair.right + 40
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("source ownership/control shape must compile");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(
        outcome
            .artifact
            .expect("a successful build must publish an artifact")
            .run_i64()
            .expect("published artifact must execute"),
        42
    );
}

#[test]
fn service_reports_overlapping_use_after_a_partial_move() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; move pair.left; pair.left }";
    let diagnostics = match StageZeroCompiler::new().compile(request(source)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("partial move overlap unexpectedly compiled: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "missing projection use-after-move diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rebuilds_and_stores_statically_selected_record_fields() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> Pair { let pair = Pair { left: 1, right: 2 }; pair.left = 42; pair }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(
        outcome.artifact.unwrap().run_record_i64().unwrap(),
        vec![42, 2]
    );
}

#[test]
fn service_rebuilds_nested_record_write_paths_from_leaf_to_root() {
    let source = "pub struct Inner { value: i64 } pub struct Outer { inner: Inner } pub fn main() -> Inner { let outer = Outer { inner: Inner { value: 1 } }; outer.inner.value = 42; outer.inner }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(
        outcome.artifact.unwrap().run_record_i64().unwrap(),
        vec![42]
    );
}

#[test]
fn service_failures_preserve_source_identity_classification_and_request_provenance() {
    let request = request("pub fn main() -> i64 { missing_name }");
    let expected_world = request.clone().normalize().unwrap().fingerprint;
    let mut reordered = request.clone();
    reordered.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("unresolved source unexpectedly compiled");
    };
    let diagnostic = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code == "G4104")
        .expect("missing-name diagnostic");
    assert_eq!(diagnostic.class, DiagnosticClass::Source);
    assert_eq!(diagnostic.severity, Severity::Error);
    assert!(
        diagnostic.primary.is_some(),
        "source diagnostic lost its span"
    );
    assert_eq!(diagnostic.input_fingerprint, Some(expected_world));
    assert_eq!(
        diagnostic.facts,
        vec![
            grandiose_stage0::DiagnosticFact {
                name: "expected".into(),
                value: "a declaration visible from the lexical scope".into(),
            },
            grandiose_stage0::DiagnosticFact {
                name: "observed".into(),
                value: "an unresolved name".into(),
            },
            grandiose_stage0::DiagnosticFact {
                name: "semantic_phase".into(),
                value: "name resolution".into(),
            },
        ]
    );
    assert_eq!(
        diagnostic.explanation,
        vec![grandiose_stage0::DiagnosticExplanationFrame {
            kind: "name-resolution".into(),
            message: "lexical lookup completed before type checking the expression".into(),
        }]
    );
}

#[test]
fn compile_diagnostic_canonicalization_is_stable_and_deduplicates_exact_facts() {
    let request = request("pub fn main() -> i64 { missing_name }");
    let file = request.sources[0].key;
    let source = grandiose_stage0::SourceSpan {
        file,
        start: 12,
        end: 24,
    };
    let duplicate = CompileDiagnostic {
        code: "G4104",
        message: "unresolved name `missing_name`".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(source),
        input_fingerprint: Some(Digest::of_bytes(b"first-world")),
        related: vec![],
        facts: vec![],
        explanation: vec![],
    };
    let same_code_different_location = CompileDiagnostic {
        primary: Some(grandiose_stage0::SourceSpan {
            start: 25,
            end: 37,
            ..source
        }),
        input_fingerprint: Some(Digest::of_bytes(b"second-world")),
        ..duplicate.clone()
    };

    let diagnostics = CompileDiagnostic::canonicalize(vec![
        same_code_different_location.clone(),
        duplicate.clone(),
        duplicate,
    ]);

    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics[0].primary, Some(source));
    assert_eq!(diagnostics[1], same_code_different_location);
}

#[test]
fn compile_diagnostic_json_lines_are_deterministic_and_escape_control_text() {
    let request = request("pub fn main() -> i64 { 0 }");
    let diagnostic = CompileDiagnostic {
        code: "G0001",
        message: "line\n\"quoted\"\\tab\t\u{001b}🙂".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Warning,
        primary: Some(grandiose_stage0::SourceSpan {
            file: request.sources[0].key,
            start: 4,
            end: 9,
        }),
        input_fingerprint: Some(Digest::of_bytes(b"json-world")),
        related: vec![],
        facts: vec![],
        explanation: vec![],
    };

    assert_eq!(
        diagnostic.to_json_line(),
        format!(
            "{{\"code\":\"G0001\",\"class\":\"source\",\"severity\":\"warning\",\"message\":\"line\\n\\\"quoted\\\"\\\\tab\\t\\u001b🙂\",\"primary\":{{\"file\":\"{}\",\"start_byte\":4,\"end_byte\":9}},\"related\":[],\"facts\":[],\"explanation\":[],\"input_fingerprint\":\"{}\"}}",
            request.sources[0].key.0,
            Digest::of_bytes(b"json-world"),
        )
    );
}

#[test]
fn compile_diagnostic_provenance_is_merged_sorted_and_rendered_independent_of_phase_order() {
    let request = request("pub fn main() -> i64 { 0 }");
    let primary = grandiose_stage0::SourceSpan {
        file: request.sources[0].key,
        start: 4,
        end: 8,
    };
    let base = CompileDiagnostic {
        code: "G0008",
        message: "a structured semantic failure".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(primary),
        input_fingerprint: None,
        related: vec![],
        facts: vec![],
        explanation: vec![],
    };
    let left = base
        .clone()
        .with_fact("observed", "open effect row")
        .with_explanation("effect-boundary", "the entrypoint has no ambient handler")
        .with_related_location(
            "effect declaration",
            grandiose_stage0::SourceSpan {
                start: 9,
                end: 12,
                ..primary
            },
        );
    let right = base
        .with_fact("expected", "closed effect row")
        .with_explanation("type-boundary", "the ABI must be fully concrete")
        .with_related_location(
            "call site",
            grandiose_stage0::SourceSpan {
                start: 13,
                end: 16,
                ..primary
            },
        );
    let first = CompileDiagnostic::canonicalize(vec![left.clone(), right.clone()]);
    let second = CompileDiagnostic::canonicalize(vec![right, left]);
    assert_eq!(first, second);
    assert_eq!(first.len(), 1);
    let diagnostic = &first[0];
    assert_eq!(
        diagnostic
            .related
            .iter()
            .map(|related| &related.label)
            .collect::<Vec<_>>(),
        vec!["call site", "effect declaration"]
    );
    assert_eq!(
        diagnostic
            .facts
            .iter()
            .map(|fact| &fact.name)
            .collect::<Vec<_>>(),
        vec!["expected", "observed"]
    );
    assert_eq!(
        diagnostic.text_lines(),
        vec![
            "G0008: a structured semantic failure".into(),
            format!("  related call site at {}:13..16", primary.file.0),
            format!("  related effect declaration at {}:9..12", primary.file.0),
            "  fact expected: closed effect row".into(),
            "  fact observed: open effect row".into(),
            "  because effect-boundary: the entrypoint has no ambient handler".into(),
            "  because type-boundary: the ABI must be fully concrete".into(),
        ]
    );
    assert!(
        diagnostic
            .to_json_line()
            .contains("\"related\":[{\"label\":\"call site\"")
    );
}

#[test]
fn compile_diagnostic_canonicalization_presents_source_facts_by_span_then_severity_and_code() {
    let request = request("pub fn main() -> i64 { missing_name }");
    let file = request.sources[0].key;
    let at_ten = grandiose_stage0::SourceSpan {
        file,
        start: 10,
        end: 11,
    };
    let at_twenty = grandiose_stage0::SourceSpan {
        file,
        start: 20,
        end: 21,
    };
    let at_ten_warning = CompileDiagnostic {
        code: "G0002",
        message: "warning at byte ten".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Warning,
        primary: Some(at_ten),
        input_fingerprint: None,
        related: vec![],
        facts: vec![],
        explanation: vec![],
    };
    let at_ten_error_later_code = CompileDiagnostic {
        code: "G0003",
        message: "later error code at byte ten".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(at_ten),
        input_fingerprint: None,
        related: vec![],
        facts: vec![],
        explanation: vec![],
    };
    let at_ten_error_earlier_code = CompileDiagnostic {
        code: "G0001",
        message: "earlier error code at byte ten".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(at_ten),
        input_fingerprint: None,
        related: vec![],
        facts: vec![],
        explanation: vec![],
    };
    let at_twenty_error = CompileDiagnostic {
        code: "G0000",
        message: "error at byte twenty".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(at_twenty),
        input_fingerprint: None,
        related: vec![],
        facts: vec![],
        explanation: vec![],
    };
    let unspanned_request = CompileDiagnostic {
        code: "G9999",
        message: "request failure".into(),
        class: DiagnosticClass::Request,
        severity: Severity::Error,
        primary: None,
        input_fingerprint: None,
        related: vec![],
        facts: vec![],
        explanation: vec![],
    };

    let diagnostics = CompileDiagnostic::canonicalize(vec![
        unspanned_request.clone(),
        at_twenty_error.clone(),
        at_ten_warning.clone(),
        at_ten_error_later_code.clone(),
        at_ten_error_earlier_code.clone(),
    ]);

    assert_eq!(
        diagnostics,
        vec![
            at_ten_error_earlier_code,
            at_ten_error_later_code,
            at_ten_warning,
            at_twenty_error,
            unspanned_request,
        ]
    );
}

#[test]
fn compile_diagnostic_span_validation_replaces_invalid_phase_locations() {
    let request = request("pub fn main() -> i64 { 42 }");
    let file = request.sources[0].key;
    let foreign_file = SourceInput::new(
        PackageKey("app@0.1.0".into()),
        LogicalPath::parse("src/foreign.glorious").unwrap(),
        b"foreign".as_slice(),
    )
    .key;
    let fingerprint = Digest::of_bytes(b"diagnostic-world");
    let valid = CompileDiagnostic {
        code: "G0001",
        message: "valid source fact".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(grandiose_stage0::SourceSpan {
            file,
            start: 0,
            end: 1,
        }),
        input_fingerprint: Some(fingerprint),
        related: vec![],
        facts: vec![],
        explanation: vec![],
    };
    let past_end = CompileDiagnostic {
        code: "G0002",
        message: "past the source end".into(),
        primary: Some(grandiose_stage0::SourceSpan {
            file,
            start: 0,
            end: 99,
        }),
        ..valid.clone()
    };
    let backwards = CompileDiagnostic {
        code: "G0003",
        message: "backwards range".into(),
        primary: Some(grandiose_stage0::SourceSpan {
            file,
            start: 3,
            end: 2,
        }),
        ..valid.clone()
    };
    let unknown_file = CompileDiagnostic {
        code: "G0004",
        message: "unknown file".into(),
        primary: Some(grandiose_stage0::SourceSpan {
            file: foreign_file,
            start: 0,
            end: 1,
        }),
        ..valid.clone()
    };

    let diagnostics = CompileDiagnostic::validate_primary_spans(
        vec![valid.clone(), past_end, backwards, unknown_file],
        &BTreeMap::from([(file, request.sources[0].bytes.len() as u32)]),
    );

    assert_eq!(diagnostics[0], valid);
    assert_eq!(diagnostics.len(), 4);
    for diagnostic in &diagnostics[1..] {
        assert_eq!(diagnostic.code, "G7014");
        assert_eq!(diagnostic.class, DiagnosticClass::Invariant);
        assert_eq!(diagnostic.severity, Severity::Error);
        assert_eq!(diagnostic.primary, None);
        assert_eq!(diagnostic.input_fingerprint, Some(fingerprint));
    }
    assert_eq!(
        diagnostics[1].message,
        "compiler produced diagnostic G0002 with an invalid source provenance span"
    );
}

#[test]
fn compile_diagnostic_error_limit_keeps_the_earliest_facts_and_reports_suppression() {
    let request = request("pub fn main() -> i64 { missing_name }");
    let file = request.sources[0].key;
    let mut diagnostics = Vec::new();
    for start in (0..5).rev() {
        diagnostics.push(CompileDiagnostic {
            code: "G4104",
            message: format!("unresolved name at byte {start}"),
            class: DiagnosticClass::Source,
            severity: Severity::Error,
            primary: Some(grandiose_stage0::SourceSpan {
                file,
                start,
                end: start + 1,
            }),
            input_fingerprint: None,
            related: vec![],
            facts: vec![],
            explanation: vec![],
        });
    }
    diagnostics.push(CompileDiagnostic {
        code: "G0002",
        message: "context warning".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Warning,
        primary: None,
        input_fingerprint: None,
        related: vec![],
        facts: vec![],
        explanation: vec![],
    });

    let diagnostics = CompileDiagnostic::limit_errors(diagnostics, 3);
    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Error)
            .count(),
        3
    );
    assert_eq!(
        diagnostics
            .iter()
            .filter_map(|diagnostic| diagnostic.primary)
            .map(|span| span.start)
            .collect::<Vec<_>>(),
        vec![0, 1]
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "G7013"
            && diagnostic.class == DiagnosticClass::Resource
            && diagnostic.message
                == "diagnostic error limit of 3 reached; 3 additional error(s) suppressed"
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.severity == Severity::Warning && diagnostic.message == "context warning"
    }));
}

#[test]
fn service_instantiates_generic_callable_signatures_at_each_direct_call() {
    let source =
        "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_explicit_generic_callable_applications() {
    let source =
        "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity<i64>(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_a_recursive_generic_scc_once_into_verified_vm_code() {
    let source = "pub fn descend<T>(value: T) -> T { descend<T>(value) } pub fn main() -> i64 { descend<i64>(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert!(
        outcome.artifact.is_some(),
        "recursive instance must verify as VM code"
    );
    let graph = outcome.instance_graph.expect("instance discovery evidence");
    let recursive = graph
        .ordered()
        .into_iter()
        .find(|instance| !instance.arguments().is_empty())
        .expect("concrete generic recursive instance");
    assert!(
        graph
            .callees(&recursive)
            .is_some_and(|callees| callees.contains(&recursive)),
        "recursive generic call must retain its concrete SCC edge: {graph:#?}"
    );
}

#[test]
fn service_materializes_generic_function_values_through_concrete_callables() {
    let source = "pub fn identity<T>(value: T) -> T { value } pub fn choose<T>() -> (T) -> T { identity } pub fn main() -> i64 { choose<i64>()(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_instantiates_non_type_direct_callable_arguments_at_the_contract_boundary() {
    for source in [
        "pub fn region<'a>() -> i64 { 0 } pub fn main() -> i64 { region<'static>() }",
        "pub fn row<e: EffectRow>() -> i64 { 0 } pub fn main() -> i64 { row<{}>() }",
        "pub fn count<n: u32>() -> i64 { 0 } pub fn main() -> i64 { count<(1 + 2)>() }",
        "pub fn count<n: u32>() -> i64 { 0 } pub fn forward<n: u32>() -> i64 { count<n + 1>() } pub fn main() -> i64 { forward<2>() }",
        "pub fn amount<q: Quantity>() -> i64 { 0 } pub fn main() -> i64 { amount<[1, 2]>() }",
    ] {
        let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
        assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
        assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 0);
    }
}

#[test]
fn service_monomorphizes_symbolic_associated_effect_row_forwarding() {
    let source = "trait Capability { type Effects: EffectRow; } struct Value { value: i64 } impl Capability for Value { type Effects = {}; } pub fn worker<T>(value: T) -> i64 / { <T as Capability>::Effects } where T: Capability { 41 } pub fn relay<T>(value: T) -> i64 / { <T as Capability>::Effects } where T: Capability { worker(value) } pub fn main() -> i64 { let value = Value { value: 0 }; relay(value) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_preserves_hrtb_callback_identity_through_symbolic_effect_forwarding() {
    let source = "trait Capability { type Effects: EffectRow; } struct Value { value: i64 } impl Capability for Value { type Effects = {}; } pub fn worker<T>(callback: for<'a> (&'a i64) -> &'a i64, value: T) -> i64 / { <T as Capability>::Effects } where T: Capability { let number = 41; callback(&number); number } pub fn relay<T>(callback: for<'a> (&'a i64) -> &'a i64, value: T) -> i64 / { <T as Capability>::Effects } where T: Capability { worker(callback, value) } pub fn main() -> i64 { 41 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_opens_higher_ranked_callback_lifetimes_without_leaking_them() {
    let accepted = "pub fn apply(callback: for<'a> (&'a i64) -> &'a i64) -> i64 { let value = 42; let loan = &value; callback(loan); value } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let escaping = "pub fn escapes(callback: for<'a> () -> &'a i64) -> i64 { callback(); 0 } pub fn main() -> i64 { 0 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(escaping))
    else {
        panic!("an escaped higher-ranked callback lifetime unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5019"),
        "missing higher-ranked lifetime leak diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_executes_hrtb_function_values_through_reference_returning_calls() {
    let source = "pub fn identity<'a>(value: &'a i64) -> &'a i64 { value } pub fn apply(callback: for<'a> (&'a i64) -> &'a i64) -> i64 { let value = 41; let result = callback(&value); *result + 1 } pub fn main() -> i64 { apply(identity) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_contextual_hrtb_closure_values_through_reference_calls() {
    let source = "pub fn apply(callback: for<'a> (&'a i64) -> &'a i64) -> i64 { let value = 41; let result = callback(&value); *result + 1 } pub fn main() -> i64 { apply({ value => value }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_hrtb_closures_with_concrete_associated_effect_projections() {
    let source = "trait Capability { type Effects<'a>: EffectRow; } struct Value {} impl Capability for Value { type Effects<'a> = {}; } pub fn apply(callback: for<'a> (&'a i64) -> &'a i64 / { <Value as Capability>::Effects<'a> }) -> i64 { let value = 41; let result = callback(&value); *result + 1 } pub fn main() -> i64 { apply({ value => value }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_imports_hrtb_associated_effect_gat_callback_contracts_through_vm() {
    let dependency = "pub trait Capability { type Effects<'a>: EffectRow; } pub struct Value {} impl Capability for Value { type Effects<'a> = {}; } pub fn apply(callback: for<'a> (&'a i64) -> &'a i64 / { <Value as Capability>::Effects<'a> }) -> i64 { let value = 41; let result = callback(&value); *result + 1 }";
    let root = "use dependency::apply; pub fn identity<'a>(value: &'a i64) -> &'a i64 { value } pub fn main() -> i64 { apply(identity) }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(root, "dependency@0.1.0", dependency))
        .expect("an imported HRTB associated-effect contract must materialize");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_inherits_hrtb_gat_callback_methods_across_dependency_traits() {
    let dependency = "pub trait Parent<T> { type Item<'a>; type Effects<'a>: EffectRow; fn apply<U>(receiver: Self, callback: for<'a> (<Self as Parent<T>>::Item<'a>) -> <Self as Parent<T>>::Item<'a> / { <Self as Parent<T>>::Effects<'a> }, marker: U) -> i64; } pub trait Child<T>: Parent<T> {} pub struct Value {} impl Parent<Value> for Value { type Item<'a> = &'a i64; type Effects<'a> = {}; fn apply<U>(receiver: Self, callback: for<'a> (<Self as Parent<Value>>::Item<'a>) -> <Self as Parent<Value>>::Item<'a> / { <Self as Parent<Value>>::Effects<'a> }, marker: U) -> i64 { let value = 41; let result = callback(&value); *result + 1 } } impl Child<Value> for Value {}";
    let root = "use dependency::Child; use dependency::Value; pub fn identity<'a>(value: &'a i64) -> &'a i64 { value } pub fn main() -> i64 { Child<Value>::apply<i64>(Value {}, identity, 0) }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(root, "dependency@0.1.0", dependency))
        .expect("inherited dependency HRTB GAT method must materialize");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_hrtb_closures_with_lifetime_gat_projections() {
    let source = "trait Family { type Item<'a>; } struct Value {} impl Family for Value { type Item<'a> = &'a i64; } pub fn apply(callback: for<'a> (<Value as Family>::Item<'a>) -> <Value as Family>::Item<'a>) -> i64 { let value = 41; let result = callback(&value); *result + 1 } pub fn main() -> i64 { apply({ value => value }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_proves_and_enforces_direct_callable_trait_bounds() {
    let accepted = "trait Sendable {} impl Sendable for i64 {} pub fn identity<T>(value: T) -> T where T: Sendable { value } pub fn main() -> i64 { identity(42) }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = "trait Sendable {} impl Sendable for i64 {} pub fn identity<T>(value: T) -> T where T: Sendable { value } pub fn main() -> Text { identity(\"not sendable\") }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(rejected))
    else {
        panic!("an unproven callable trait bound unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4143"),
        "missing callable trait-bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_uses_declared_auto_traits_at_callable_boundaries() {
    let accepted = "auto trait Sendish {} struct Pair { value: i64 } pub fn require<T>(value: T) -> i64 where T: Sendish { 7 } pub fn main() -> i64 { require(Pair { value: 1 }) }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 7);

    let rejected = "auto trait Sendish {} impl !Sendish for Text {} pub fn require<T>(value: T) -> i64 where T: Sendish { 7 } pub fn main() -> i64 { require(\"denied\") }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(rejected))
    else {
        panic!("an explicitly negative auto-trait bound unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4142"),
        "missing explicit auto-trait rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_overlapping_positive_and_negative_trait_implementations() {
    // Coherence must reject the conflicting pair before any source body can
    // rely on either answer.  The solver and coherence unit suites cover the
    // head-unification algorithm; this confirms that a user program cannot
    // reach the executable artifact boundary with contradictory evidence.
    let source = "trait Marker<T> {} struct Box<T> {} impl<T> Marker<T> for Box<T> {} impl !Marker<i64> for Box<i64> {} pub fn main() -> i64 { 42 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("contradictory positive and negative trait implementations unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3406"),
        "missing mixed-polarity coherence diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_uses_implementation_where_bounds_while_type_checking_method_bodies() {
    let source = "trait Mark {} pub fn requires_mark<T>(value: T) -> T where T: Mark { value } trait Relay<T> { fn relay(value: T) -> T; } impl<T> Relay<T> for i64 where T: Mark { fn relay(value: T) -> T { requires_mark(value) } } impl Mark for i64 {} pub fn main() -> i64 { Relay<i64>::relay(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_runs_generic_subtrait_impls_proven_by_their_where_contract() {
    let source = "trait Gate {} trait Parent<T> { fn identity(value: T) -> T; } trait Child<T>: Parent<T> {} impl Gate for i64 {} impl<T> Parent<T> for T where T: Gate { fn identity(value: T) -> T { value } } impl<T> Child<T> for T where T: Gate {} pub fn main() -> i64 { Child<i64>::identity(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_uses_generic_child_bounds_to_discharge_parent_callable_contracts() {
    let source = "trait Parent {} trait Child: Parent {} pub fn requires_parent<T>(value: T) -> T where T: Parent { value } pub fn relay<T>(value: T) -> T where T: Child { requires_parent(value) } impl Parent for i64 {} impl Child for i64 {} pub fn main() -> i64 { relay(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_type_checks_implementation_method_bodies() {
    let source = "trait Convert { fn convert(value: i64) -> i64; } impl Convert for i64 { fn convert(value: i64) -> i64 { \"not an integer\" } } pub fn main() -> i64 { 42 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("ill-typed implementation method unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4110"),
        "missing implementation method result diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_type_checks_implementation_method_bodies_with_impl_generics() {
    let source = "trait Identity<T> { fn identity(value: T) -> T; } struct Box<T> {} impl<T> Identity<T> for Box<T> { fn identity(value: T) -> T { value } } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_normalizes_concrete_associated_const_signature_projections_before_vm() {
    let source = "trait Width { const Value: u32; } pub struct Chosen<n: u32> {} impl Width for i64 { const Value = 7; } pub fn mirror(value: Chosen<<i64 as Width>::Value>) -> Chosen<<i64 as Width>::Value> { value } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_recursively_normalizes_associated_const_projection_values_before_vm() {
    let source = "trait First { const Value: u32; } trait Second { const Value: u32; } pub struct Chosen<n: u32> {} impl Second for i64 { const Value = 7; } impl First for i64 { const Value = <i64 as Second>::Value; } pub fn mirror(value: Chosen<<i64 as First>::Value>) -> Chosen<<i64 as First>::Value> { value } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_unselected_concrete_associated_const_signature_projection() {
    let source = "trait Width { const Value: u32; } pub struct Chosen<n: u32> {} pub fn invalid(value: Chosen<<i64 as Width>::Value>) -> i64 { 0 } pub fn main() -> i64 { 42 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("unselected associated const signature projection entered an artifact");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| matches!(diagnostic.code, "G4152" | "G4190")),
        "missing concrete associated-const selection diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_selects_and_executes_explicit_trait_method_calls() {
    let source = "trait Increment { fn increment(value: i64) -> i64; } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 1 } } pub fn main() -> i64 { Increment::increment(41) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_contextually_typed_trait_method_values() {
    let source = "trait Increment { fn increment(value: i64) -> i64; } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 1 } } pub fn apply(callable: (i64) -> i64) -> i64 { callable(41) } pub fn main() -> i64 { apply(Increment::increment) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_unconstrained_trait_method_value_generics_at_the_core_boundary() {
    let source = "trait Pick { fn pick<T>(value: i64) -> i64; } impl Pick for i64 { fn pick<T>(value: i64) -> i64 { value } } pub fn accept(callable: (i64) -> i64) -> i64 { callable(42) } pub fn main() -> i64 { accept(Pick::pick) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("unconstrained trait-method generic unexpectedly entered an artifact");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4116"),
        "missing frozen-Core inference diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_direct_qualified_trait_calls_without_a_selected_implementation() {
    let source = "trait Increment { fn increment(value: i64) -> i64; } pub fn main() -> i64 { Increment::increment(41) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("trait call without an implementation unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4169"),
        "missing selected-trait diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_overlapping_direct_qualified_trait_call_candidates_at_coherence() {
    let source = "trait Increment { fn increment(value: i64) -> i64; } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 1 } } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 2 } } pub fn main() -> i64 { Increment::increment(40) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("overlapping trait implementations unexpectedly compiled");
    };
    let diagnostic = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code == "G3404")
        .expect("missing trait coherence diagnostic");
    assert_eq!(
        diagnostic.facts,
        vec![grandiose_stage0::DiagnosticFact {
            name: "semantic_phase".into(),
            value: "trait coherence".into(),
        }]
    );
    assert_eq!(diagnostic.related.len(), 1, "{diagnostic:#?}");
    assert_eq!(diagnostic.related[0].label, "conflicting implementation");
    assert_ne!(diagnostic.related[0].span, diagnostic.primary.unwrap());
    assert_eq!(
        diagnostic.explanation,
        vec![grandiose_stage0::DiagnosticExplanationFrame {
            kind: "coherence".into(),
            message: "the two frozen implementation heads can apply to the same trait goal".into(),
        }]
    );
}

#[test]
fn service_selects_trait_methods_using_the_implicit_self_receiver_type() {
    let source = "trait Increment { fn increment(value: Self) -> Self; } impl Increment for i64 { fn increment(value: Self) -> Self { value + 1 } } pub fn main() -> i64 { Increment::increment(41) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_selects_generic_qualified_trait_method_arguments() {
    let source = "trait Replace { fn replace<T>(value: i64, replacement: T) -> T; } impl Replace for i64 { fn replace<T>(value: i64, replacement: T) -> T { replacement } } pub fn main() -> Text { Replace::replace(0, \"selected\") }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_text().unwrap(), "selected");
}

#[test]
fn service_selects_explicit_trait_method_operation_arguments() {
    let source = "trait Replace { fn replace<T>(value: i64, replacement: T) -> T; } impl Replace for i64 { fn replace<T>(value: i64, replacement: T) -> T { replacement } } pub fn main() -> Text { Replace::replace<Text>(0, \"selected\") }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_text().unwrap(), "selected");
}

#[test]
fn service_selects_trait_methods_with_mixed_non_type_operation_arguments() {
    let source = "trait Relay { fn relay<'a, e: EffectRow, n: u32, q: Quantity>(receiver: i64) -> i64 / {| e}; } impl Relay for i64 { fn relay<'a, e: EffectRow, n: u32, q: Quantity>(receiver: i64) -> i64 / {| e} { receiver } } pub fn main() -> i64 { Relay::relay<'static, {}, 7, [1, 1]>(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_selects_generic_qualified_trait_instances() {
    let source = "trait Identity<T> { fn identity(value: T) -> T; } impl<T> Identity<T> for T { fn identity(value: T) -> T { value } } pub fn main() -> i64 { Identity<i64>::identity(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
    assert!(
        outcome
            .instance_graph
            .expect("selected trait method must materialize an instance")
            .ordered()
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
}

#[test]
fn service_materializes_generic_trait_methods_with_associated_type_and_const_layouts() {
    let source = "trait Recipe<T> { type Item; const Width: u32; fn replace<U>(value: T, replacement: U) -> U; } pub struct Witness<n: u32> { value: i64 } impl Recipe<i64> for i64 { type Item = i64; const Width = 7; fn replace<U>(value: i64, replacement: U) -> U { replacement } } pub fn package<U>(value: <i64 as Recipe<i64>>::Item, replacement: U) -> U { let witness = Witness<<i64 as Recipe<i64>>::Width> { value: value }; Recipe<i64>::replace(witness.value, replacement) } pub fn main() -> Text { let selected = \"trait dictionary\"; package(0, move selected) }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("concrete evidence must materialize the generic trait method and projections");
    assert_eq!(
        outcome
            .artifact
            .expect("build must publish a VM artifact")
            .run_text()
            .unwrap(),
        "trait dictionary"
    );
    assert!(
        outcome
            .instance_graph
            .expect("generic public wrapper and selected trait method are instances")
            .ordered()
            .iter()
            .filter(|instance| !instance.arguments().is_empty())
            .count()
            >= 2,
        "both the public wrapper and its evidence-selected generic method must materialize"
    );
}

#[test]
fn service_materializes_selected_trait_method_values_from_callable_context() {
    let source = "trait Increment { fn increment(value: i64) -> i64; } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 1 } } pub fn apply(function: (i64) -> i64) -> i64 { function(41) } pub fn main() -> i64 { apply(Increment::increment) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
    assert!(
        outcome
            .instance_graph
            .expect("selected trait method value must materialize an instance")
            .ordered()
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
}

#[test]
fn service_materializes_generic_selected_trait_method_values_from_callable_context() {
    let source = "trait Replace { fn replace<T>(value: i64, replacement: T) -> T; } impl Replace for i64 { fn replace<T>(value: i64, replacement: T) -> T { replacement } } pub fn apply(function: (i64, Text) -> Text) -> Text { function(0, \"selected\") } pub fn main() -> Text { apply(Replace::replace) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_text().unwrap(), "selected");
    assert!(
        outcome
            .instance_graph
            .expect("generic selected trait method value must materialize an instance")
            .ordered()
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
}

#[test]
fn service_enforces_selected_trait_method_where_bounds() {
    let accepted = "trait Mark {} trait Convert { fn convert<T>(receiver: i64, value: T) -> T where T: Mark; } impl Mark for i64 {} impl Convert for i64 { fn convert<T>(receiver: i64, value: T) -> T where T: Mark { value } } pub fn main() -> i64 { Convert::convert(0, 42) }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = "trait Mark {} trait Convert { fn convert<T>(receiver: i64, value: T) -> T where T: Mark; } impl Mark for i64 {} impl Convert for i64 { fn convert<T>(receiver: i64, value: T) -> T where T: Mark { value } } pub fn main() -> Text { Convert::convert(0, \"not marked\") }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(rejected))
    else {
        panic!("unproven trait method bound unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4143"),
        "missing trait method bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_enforces_selected_trait_method_associated_type_bindings() {
    let accepted = "trait Shape { type Item; } trait Keep { fn keep<T>(receiver: i64, value: T) -> i64 where T: Shape<Item = i64>; } impl Shape for i64 { type Item = i64; } impl Keep for i64 { fn keep<T>(receiver: i64, value: T) -> i64 where T: Shape<Item = i64> { receiver + 1 } } pub fn main() -> i64 { Keep::keep(41, 0) }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = "trait Shape { type Item; } trait Keep { fn keep<T>(receiver: i64, value: T) -> i64 where T: Shape<Item = i64>; } impl Shape for Text { type Item = Text; } impl Keep for i64 { fn keep<T>(receiver: i64, value: T) -> i64 where T: Shape<Item = i64> { receiver + 1 } } pub fn main() -> i64 { Keep::keep(41, \"wrong\") }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(rejected))
    else {
        panic!("trait method accepted a mismatched associated type binding");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4143"),
        "missing trait method associated-binding diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_enforces_selected_trait_method_associated_effect_bindings() {
    let accepted = "trait Capability { type Effects: EffectRow; } trait Keep { fn keep<T>(receiver: i64, value: T) -> i64 where T: Capability<Effects = {}>; } impl Capability for i64 { type Effects = {}; } impl Keep for i64 { fn keep<T>(receiver: i64, value: T) -> i64 where T: Capability<Effects = {}> { receiver + 1 } } pub fn main() -> i64 { Keep::keep(41, 0) }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = "effect Log { note(); } trait Capability { type Effects: EffectRow; } trait Keep { fn keep<T>(receiver: i64, value: T) -> i64 where T: Capability<Effects = {}>; } impl Capability for Text { type Effects = { Log }; } impl Keep for i64 { fn keep<T>(receiver: i64, value: T) -> i64 where T: Capability<Effects = {}> { receiver + 1 } } pub fn main() -> i64 { Keep::keep(41, \"wrong\") }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(rejected))
    else {
        panic!("trait method accepted a mismatched associated effect-row binding");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4143"),
        "missing trait method associated effect-binding diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_enforces_trait_method_value_associated_bindings() {
    let accepted = "trait Shape { type Item; } trait Keep { fn keep<T>(receiver: i64, value: T) -> i64 where T: Shape<Item = i64>; } impl Shape for i64 { type Item = i64; } impl Keep for i64 { fn keep<T>(receiver: i64, value: T) -> i64 where T: Shape<Item = i64> { receiver + 1 } } pub fn apply(callable: (i64, i64) -> i64) -> i64 { callable(41, 0) } pub fn main() -> i64 { apply(Keep::keep) }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = "trait Shape { type Item; } trait Keep { fn keep<T>(receiver: i64, value: T) -> i64 where T: Shape<Item = i64>; } impl Shape for Text { type Item = Text; } impl Keep for i64 { fn keep<T>(receiver: i64, value: T) -> i64 where T: Shape<Item = i64> { receiver + 1 } } pub fn apply(callable: (i64, Text) -> i64) -> i64 { callable(41, \"wrong\") } pub fn main() -> i64 { apply(Keep::keep) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(rejected))
    else {
        panic!("trait method value accepted a mismatched associated type binding");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4143"),
        "missing trait method value associated-binding diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_instantiates_nominal_field_associated_type_projections() {
    let source = "trait Has { type Item; } impl Has for i64 { type Item = i64; } pub struct Box { item: <i64 as Has>::Item } type Alias = Box; pub fn unwrap(value: Alias) -> i64 { value.item + 1 } pub fn main() -> i64 { unwrap(Box { item: 41 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = "trait Has { type Item; } impl Has for i64 { type Item = Text; } pub struct Box { item: <i64 as Has>::Item } pub fn main() -> i64 { let value = Box { item: 41 }; 0 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(rejected))
    else {
        panic!("a nominal field projection accepted the wrong concrete item type");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4126"),
        "missing instantiated nominal field mismatch diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_lowers_concrete_gat_type_projections_through_vm_layouts() {
    let source = "trait Family { type Item<T>; } impl Family for i64 { type Item<T> = T; } pub struct Packet { value: <i64 as Family>::Item<i64> } pub fn increment(value: <i64 as Family>::Item<i64>) -> i64 { value + 1 } pub fn main() -> i64 { let packet = Packet { value: 41 }; increment(packet.value) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_defaulted_gat_type_projections_through_vm_layouts() {
    // The selected impl deliberately omits `Item`: source layout elaboration
    // must instantiate the trait's generic default rather than treating the
    // projection as an unresolved abstract type.
    let source = "trait Family { type Item<T> = T; } struct Value {} impl Family for Value {} pub struct Packet { value: <Value as Family>::Item<i64> } pub fn increment(value: <Value as Family>::Item<i64>) -> i64 { value + 1 } pub fn main() -> i64 { let packet = Packet { value: 41 }; increment(packet.value) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_instantiates_structural_const_nominal_layouts_at_record_construction() {
    let source = "pub struct Carrier<n: u32, T> { value: T } pub fn main() -> i64 { let value = Carrier<7, i64> { value: 41 }; value.value + 1 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_specializes_trait_method_effect_identities_with_quantity_generics() {
    let source = "effect Pulse<n: u32> { ask() -> i64; } trait Relay { fn relay<n: u32>(receiver: i64) -> i64 / { Pulse<n> }; } impl Relay for i64 { fn relay<n: u32>(receiver: i64) -> i64 / { Pulse<n> } { Pulse<n>::ask() } } pub fn main() -> i64 { handle Relay::relay<7>(0) { Pulse<7>::ask() with k => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_normalizes_concrete_associated_effect_rows_on_trait_method_values() {
    let source = "effect Trace { note() -> i64; } trait Capability { type Effects: EffectRow; } impl Capability for i64 { type Effects = {Trace}; } trait Relay { fn relay(receiver: i64) -> i64 / { <i64 as Capability>::Effects }; } impl Relay for i64 { fn relay(receiver: i64) -> i64 / { <i64 as Capability>::Effects } { Trace::note() } } pub fn apply(callable: (i64) -> i64 / Trace) -> i64 / Trace { callable(0) } pub fn main() -> i64 { handle apply(Relay::relay) { Trace::note() with k => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_concrete_associated_effect_gats_through_vm_handlers() {
    let source = "effect Trace<T> { [1,1] note(value: T) -> i64; } trait Capability { type Effects<T>: EffectRow; } impl Capability for i64 { type Effects<T> = {Trace<T>}; } pub fn worker() -> i64 / { <i64 as Capability>::Effects<i64> } { Trace<i64>::note(41) } pub fn main() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_defaulted_associated_effect_gats_through_vm_handlers() {
    // As above, this uses the trait-level GAT default, but its normalized row
    // crosses method-effect checking, handler selection, VM emission, and
    // execution rather than stopping at solver normalization.
    let source = "effect Trace<T> { [1,1] note(value: T) -> i64; } trait Capability { type Effects<T>: EffectRow = {Trace<T>}; } struct Value {} impl Capability for Value {} pub fn worker() -> i64 / { <Value as Capability>::Effects<i64> } { Trace<i64>::note(41) } pub fn main() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_inherited_gat_types_effect_rows_and_methods_through_vm() {
    // `Child` owns none of these items.  Selection must walk its instantiated
    // Parent edge consistently for the method, the layout-bearing GAT, and
    // the handler-visible associated effect row.
    let dependency = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay(value: T) -> T; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = U; type Effects<U> = {Trace<U>}; fn relay(value: i64) -> i64 { value } } impl Child<i64> for i64 {}";
    let root = "use dependency::Child; use dependency::Trace; pub struct Packet { value: <i64 as Child<i64>>::Item<i64> } pub fn worker() -> i64 / { <i64 as Child<i64>>::Effects<i64> } { let packet = Packet { value: Child<i64>::relay(41) }; Trace<i64>::note(packet.value) } pub fn main() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(root, "dependency@0.1.0", dependency))
        .expect("inherited associated items must materialize through the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_reexported_hrtb_inherited_effect_gats_through_vm_handlers() {
    let mut request = request(
        "use bridge::Child; use bridge::Trace; pub fn relay<'a>(value: &'a i64) -> &'a i64 / { <&'a i64 as Child<i64>>::Effects<'a> } { Child<i64>::relay(value) } pub fn apply(callback: for<'a> (&'a i64) -> &'a i64 / { <&'a i64 as Child<i64>>::Effects<'a> }) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); Trace<i64>::note(*result) } pub fn main() -> i64 { handle apply(relay) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Child, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Effects<'a>: EffectRow; fn relay<'a>(receiver: &'a T) -> &'a T / Trace<i64>; } pub trait Child<T>: Parent<T> {} impl<'a> Parent<i64> for &'a i64 { type Effects<'b> = {Trace<i64>}; fn relay<'b>(receiver: &'b i64) -> &'b i64 / Trace<i64> { Trace<i64>::note(*receiver); receiver } } impl<'a> Child<i64> for &'a i64 {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("a reexported inherited HRTB method must retain its associated effect GAT");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_recursive_defaulted_hrtb_supertrait_gats_through_vm() {
    // Both public GAT defaults recursively project through a second default
    // on the selected parent implementation. `Gateway` exposes only the
    // child facade, whose where clause establishes that parent contract.
    // The HRTB callback forces both the type and row defaults through alias
    // resolution, method selection, handler checking, and VM materialization.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn bounce<'a>(value: &'a i64) -> &'a i64 / { <&'a i64 as Capability<i64>>::Effects<'a> } { Capability<i64>::relay(value) } pub fn apply(callback: for<'a> (&'a i64) -> &'a i64 / { <&'a i64 as Capability<i64>>::Effects<'a> }) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); Trace<i64>::note(*result) } pub fn main() -> i64 { handle apply(bounce) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Child as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Base<'a> = &'a T; type Item<'a> = <Self as Parent<T>>::Base<'a>; type BaseEffects<'a>: EffectRow = {Trace<i64>}; type Effects<'a>: EffectRow = { <Self as Parent<T>>::BaseEffects<'a> }; fn relay<'a>(value: <Self as Parent<T>>::Item<'a>) -> <Self as Parent<T>>::Item<'a> / { <Self as Parent<T>>::Effects<'a> }; } pub trait Child<T>: Parent<T> {} impl<'r> Parent<i64> for &'r i64 { fn relay<'a>(value: &'a i64) -> &'a i64 / {Trace<i64>} { Trace<i64>::note(*value); value } } impl<'r> Child<i64> for &'r i64 where &'r i64: Parent<i64> {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("selected recursive defaulted supertrait GATs must materialize into the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_unselected_recursive_defaulted_hrtb_supertrait_gats() {
    // Keep the same nested defaults and HRTB projection, but leave the parent
    // unimplemented.  The child's scoped `where` declaration is a contract,
    // not global evidence: validation and projection normalization must reach
    // a finite rejected state rather than treating defaults as an impl.
    let mut request = request(
        "use bridge::Gateway as Capability; pub fn bounce<'a>(value: &'a i64) -> &'a i64 / { <&'a i64 as Capability<i64>>::Effects<'a> } { value } pub fn main() -> i64 { let value = 41; *bounce(&value) }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::Child as Gateway;".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Base<'a> = &'a T; type Item<'a> = <Self as Parent<T>>::Base<'a>; type BaseEffects<'a>: EffectRow = {Trace<i64>}; type Effects<'a>: EffectRow = { <Self as Parent<T>>::BaseEffects<'a> }; } pub trait Child<T>: Parent<T> {} impl<'r> Child<i64> for &'r i64 where &'r i64: Parent<i64> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("unselected recursive defaulted HRTB GATs unexpectedly reached VM emission");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G4190"),
        "missing unselected recursive default projection rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_executes_defaulted_hrtb_type_to_effect_gats_through_aliased_supertraits() {
    // `Effects` is defaulted in terms of the selected `Item` GAT.  The
    // public alias sees only Child, whose scoped parent contract provides
    // the selected implementation.  HRTB use carries the resulting type and
    // effect identities all the way through handler dispatch and the VM.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn identity<'a>(value: &'a i64) -> &'a i64 / Trace<i64> { value } pub fn apply(callback: for<'a> (&'a i64) -> &'a i64 / { <&'a i64 as Capability<i64>>::Effects<'a> }) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); Trace<i64>::note(*result) } pub fn main() -> i64 { handle apply(identity) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Child as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<'a> = i64; type Effects<'a>: EffectRow = {Trace<<Self as Parent<T>>::Item<'a>>}; } pub trait Child<T>: Parent<T> {} impl<'r> Parent<i64> for &'r i64 {} impl<'r> Child<i64> for &'r i64 where &'r i64: Parent<i64> {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("defaulted HRTB type-to-effect GATs must reach the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_mutually_defaulted_hrtb_gat_rows_without_forging_an_effect() {
    // Here `Effects` feeds itself to the row generic of `Item`. Even though
    // the Item default erases that argument, the requested row is cyclic as
    // written. The compiler must end in a finite source rejection—not loop
    // and not claim that `Trace<&i64>` is an admitted effect.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn worker<'a>(value: &'a i64) -> i64 / { <&'a i64 as Capability<i64>>::Effects<'a> } { Trace<&'a i64>::note(value) } pub fn main() -> i64 { 42 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Child as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<'a, row: EffectRow> = &'a T; type Effects<'a>: EffectRow = {Trace<<Self as Parent<T>>::Item<'a, { <Self as Parent<T>>::Effects<'a> }>>}; } pub trait Child<T>: Parent<T> {} impl<'r> Parent<i64> for &'r i64 {} impl<'r> Child<i64> for &'r i64 where &'r i64: Parent<i64> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("mutually defaulted HRTB GAT row unexpectedly entered VM emission");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G4155"),
        "missing finite cyclic defaulted-row rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_alias_equivalent_polarity_for_defaulted_hrtb_gats() {
    // Alias spelling cannot let a positive defaulted implementation coexist
    // with a negative implementation of the same HRTB GAT-bearing trait.
    let mut request = request(
        "use bridge::{First as Positive, Second as Negative}; pub struct Local {} impl Positive<i64> for Local {} impl !Negative<i64> for Local {} pub fn main() -> i64 { 42 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Capability as First, Capability as Second};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Capability<T> { type Item<'a> = &'a T; type Effects<'a>: EffectRow = {Trace<<Self as Capability<T>>::Item<'a>>}; }".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("alias-equivalent positive and negative defaulted GAT impls coexisted");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G3406"),
        "missing mixed-polarity defaulted-GAT coherence rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_executes_three_level_defaulted_hrtb_gats_with_const_and_row_arguments() {
    // The public facade is the third trait in the chain; both GAT defaults
    // belong to Base. Their explicit lifetime, effect-row, and const inputs
    // must survive inherited lookup, scoped impl obligations, an HRTB
    // callback, and VM handler identity materialization.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn identity<'a>(value: &'a i64) -> &'a i64 / Trace<7, i64> { value } pub fn apply(callback: for<'a> (&'a i64) -> &'a i64 / { <&'a i64 as Capability<i64>>::Effects<'a, {}, 7> }) -> i64 / Trace<7, i64> { let value = 41; let result = callback(&value); Trace<7, i64>::note(*result) } pub fn main() -> i64 { handle apply(identity) { Trace<7, i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<n: u32, T> { [1,1] note(value: T) -> i64; } pub trait Base<T> { type Item<'a, row: EffectRow, n: u32> = i64; type Effects<'a, row: EffectRow, n: u32>: EffectRow = {Trace<n, <Self as Base<T>>::Item<'a, row, n>>, | row}; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl<'r> Base<i64> for &'r i64 {} impl<'r> Middle<i64> for &'r i64 where &'r i64: Base<i64> {} impl<'r> Top<i64> for &'r i64 where &'r i64: Middle<i64> {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("three-level inherited defaulted HRTB GATs must reach the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_three_level_defaulted_hrtb_gat_alias_mixed_polarity() {
    // These aliases name the same third-level trait. The positive impl would
    // otherwise inherit Base's defaulted HRTB GATs, while the negative alias
    // denies that same selected fact. Explicit row/const application must
    // preserve the refutation rather than choosing an alias-specific default.
    let mut request = request(
        "use bridge::{Base, Middle, First as Positive, Second as Negative, Trace}; pub struct Local {} impl Base<i64> for Local {} impl Middle<i64> for Local where Local: Base<i64> {} impl Positive<i64> for Local where Local: Middle<i64> {} impl !Negative<i64> for Local {} pub fn probe<'a>(value: &'a i64) -> i64 / { <Local as Positive<i64>>::Effects<'a, {}, 7> } { Trace<7, i64>::note(41) } pub fn main() -> i64 { 42 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Base, Middle, Top as First, Top as Second, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<n: u32, T> { [1,1] note(value: T) -> i64; } pub trait Base<T> { type Item<'a, row: EffectRow, n: u32> = i64; type Effects<'a, row: EffectRow, n: u32>: EffectRow = {Trace<n, <Self as Base<T>>::Item<'a, row, n>>, | row}; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("mixed-polarity three-level defaulted GAT aliases entered VM emission");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G3406"),
        "missing mixed-polarity three-level alias coherence rejection: {diagnostics:#?}"
    );
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G4192"),
        "missing bounded ambiguous defaulted effect-GAT projection: {diagnostics:#?}"
    );
}

#[test]
fn service_materializes_three_level_defaulted_gat_trait_method_values_through_vm() {
    // `relay` belongs to Base but is extracted through the Top facade as an
    // indirect callable. Its explicit effect-row/const generic arguments
    // select Base's HRTB GAT defaults, so method materialization cannot lose
    // either the inherited owner or the concrete defaulted effect identity.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn apply(callback: (i64) -> i64 / Trace<7, i64>) -> i64 / Trace<7, i64> { callback(41) } pub fn main() -> i64 { handle apply(Capability<i64>::relay) { Trace<7, i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<n: u32, T> { [1,1] note(value: T) -> i64; } pub trait Base<T> { type Item<'a, row: EffectRow, n: u32> = i64; type Effects<'a, row: EffectRow, n: u32>: EffectRow = {Trace<n, <Self as Base<T>>::Item<'a, row, n>>, | row}; fn relay(value: i64) -> i64 / { <Self as Base<T>>::Effects<'static, {}, 7> }; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Base<i64> for i64 { fn relay(value: i64) -> i64 / { <i64 as Base<i64>>::Effects<'static, {}, 7> } { Trace<7, i64>::note(value) } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("inherited defaulted-GAT method values must materialize into the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_mixed_polarity_three_level_defaulted_method_values_through_aliases() {
    // The extracted method is inherited from Base, but its requested callable
    // identity begins at the Top alias. A conflicting negative alias must
    // block that materialization just as it blocks direct defaulted-GAT
    // projection selection.
    let mut request = request(
        "use bridge::{Base, Middle, First as Positive, Second as Negative, Trace}; pub struct Local {} impl Base<i64> for Local { fn relay(value: i64) -> i64 / { <Local as Base<i64>>::Effects<'static, {}, 7> } { Trace<7, i64>::note(value) } } impl Middle<i64> for Local where Local: Base<i64> {} impl Positive<i64> for Local where Local: Middle<i64> {} impl !Negative<i64> for Local {} pub fn apply(callback: (i64) -> i64 / Trace<7, i64>) -> i64 / Trace<7, i64> { callback(41) } pub fn main() -> i64 { handle apply(Positive<i64>::relay) { Trace<7, i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Base, Middle, Top as First, Top as Second, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<n: u32, T> { [1,1] note(value: T) -> i64; } pub trait Base<T> { type Item<'a, row: EffectRow, n: u32> = i64; type Effects<'a, row: EffectRow, n: u32>: EffectRow = {Trace<n, <Self as Base<T>>::Item<'a, row, n>>, | row}; fn relay(value: i64) -> i64 / { <Self as Base<T>>::Effects<'static, {}, 7> }; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("mixed-polarity inherited method value unexpectedly entered VM emission");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G3406"),
        "missing mixed-polarity inherited method-value coherence rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_forwards_open_rows_from_inherited_hrtb_gat_method_values_to_handlers() {
    // The method value is inherited through two public supertrait edges. Its
    // associated row default retains `e` open under an HRTB; `forward` then
    // carries that exact row to the outer handler, which instantiates it at
    // the call site. No stage may prematurely close or erase `e`.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn forward<e: EffectRow>(callback: (i64) -> i64 / {Trace<i64>, | e}) -> i64 / {Trace<i64>, | e} { let result = callback(41); Trace<i64>::note(result) } pub fn main() -> i64 { handle forward<{}>(Capability<i64>::relay) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Base<T> { type Item<'a, e: EffectRow> = i64; type Effects<'a, e: EffectRow>: EffectRow = {Trace<i64>, | e}; fn relay(value: i64) -> i64 / { <Self as Base<T>>::Effects<'static, {}> }; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Base<i64> for i64 { fn relay(value: i64) -> i64 / { <i64 as Base<i64>>::Effects<'static, {}> } { value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("inherited HRTB method values must forward their open defaulted rows");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_inherited_hrtb_static_trait_method_values_through_vm() {
    // `relay` is static: its first argument is borrowed data, not `Self`.
    // The qualified `Top::relay` value must therefore select its unique
    // concrete implementation rather than treating `&'a i64` as the trait
    // subject. The HRTB proves that the selected lifetime remains callable.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn apply(callback: for<'a> (&'a i64) -> i64 / Trace<i64>) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); Trace<i64>::note(result) } pub fn main() -> i64 { handle apply(Capability<i64>::relay) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Base<T> { type Effects<'a>: EffectRow = {Trace<i64>}; fn relay<'a>(value: &'a i64) -> i64 / { <Self as Base<T>>::Effects<'a> }; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Base<i64> for i64 { fn relay<'a>(value: &'a i64) -> i64 / { <i64 as Base<i64>>::Effects<'a> } { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("inherited HRTB static method values must materialize into the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_ambiguous_aliased_inherited_hrtb_static_method_values() {
    // Unlike the unique case above, `Gateway<i64>` has two concrete subjects
    // that inherit the same static HRTB method. Its first callable parameter
    // is data rather than `Self`, so it must not secretly pick either subject
    // while crossing the public alias and supertrait edges.
    let mut request = request(
        "use bridge::Gateway as Capability; pub fn apply(callback: for<'a> (&'a i64) -> i64) -> i64 { let value = 41; callback(&value) + 1 } pub fn main() -> i64 { apply(Capability<i64>::relay) }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::Top as Gateway;".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub trait Base<T> { fn relay<'a>(value: &'a i64) -> i64; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Base<i64> for i64 { fn relay<'a>(value: &'a i64) -> i64 { *value } } impl Base<i64> for u64 { fn relay<'a>(value: &'a i64) -> i64 { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Middle<i64> for u64 where u64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {} impl Top<i64> for u64 where u64: Middle<i64> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("ambiguous static trait method value unexpectedly entered VM emission");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G4169"),
        "missing ambiguous static trait method-value rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_materializes_unique_hrtb_static_method_values_with_defaulted_gats_and_negative_peers() {
    // `Top<i64>` has one positive subject and a distinct negative peer. The
    // inherited static method's HRTB effect projects a default using all
    // three item domains: lifetime, effect row, and structural const. The
    // public alias must retain that identity, while the negative peer must
    // neither become a candidate nor poison the selected positive evidence.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn apply(callback: for<'a> (&'a i64) -> i64 / Trace<7, i64>) -> i64 / Trace<7, i64> { let value = 41; let result = callback(&value); Trace<7, i64>::note(result) } pub fn main() -> i64 { handle apply(Capability<i64>::relay) { Trace<7, i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<n: u32, T> { [1,1] note(value: T) -> i64; } pub trait Base<T> { type Item<'a, row: EffectRow, n: u32> = i64; type Effects<'a, row: EffectRow, n: u32>: EffectRow = {Trace<n, <Self as Base<T>>::Item<'a, row, n>>, | row}; fn relay<'a>(value: &'a i64) -> i64 / { <Self as Base<T>>::Effects<'a, {}, 7> }; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Base<i64> for i64 { fn relay<'a>(value: &'a i64) -> i64 / { <i64 as Base<i64>>::Effects<'a, {}, 7> } { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {} impl !Top<i64> for u64 {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("unique defaulted-GAT static HRTB method value must reach the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_static_hrtb_method_values_with_overlapping_gat_constrained_blankets() {
    // The exact `i64` implementation and the blanket implementation both
    // apply: `i64` proves `Gate` with precisely the row required by the
    // blanket's GAT equality. Static method-value extraction cannot treat the
    // exact head as unique merely because the other candidate is generic.
    let mut request = request(
        "use bridge::Gateway as Capability; pub fn apply(callback: for<'a> (&'a i64) -> i64 / Trace<7, i64>) -> i64 / Trace<7, i64> { let value = 41; callback(&value) } pub fn main() -> i64 { apply(Capability<i64>::relay) }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<n: u32, T> { [1,1] note(value: T) -> i64; } pub trait Gate { type Effects<'a>: EffectRow; } pub trait Base<T> { type Effects<'a>: EffectRow = {Trace<7, i64>}; fn relay<'a>(value: &'a i64) -> i64 / { <Self as Base<T>>::Effects<'a> } where Self: Gate<Effects<'static> = {Trace<7, i64>}>; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Gate for i64 { type Effects<'a> = {Trace<7, i64>}; } impl Base<i64> for i64 { fn relay<'a>(value: &'a i64) -> i64 / {Trace<7, i64>} where i64: Gate<Effects<'static> = {Trace<7, i64>}> { *value } } impl<U> Base<i64> for U where U: Gate { fn relay<'a>(value: &'a i64) -> i64 / {Trace<7, i64>} where U: Gate<Effects<'static> = {Trace<7, i64>}> { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("overlapping GAT-constrained blanket unexpectedly entered VM emission");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G3404"),
        "missing overlapping GAT-constrained blanket coherence rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_negative_supertrait_hrtb_static_method_values_with_gat_row_equality() {
    // Base has positive evidence and its static method carries a generic GAT
    // row equality. Top explicitly negates the same subject, so extracting
    // the method through the Top alias must not fall back to Base's positive
    // implementation and must never emit a VM artifact.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn apply(callback: for<'a> (&'a i64) -> i64 / Trace<i64>) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); Trace<i64>::note(result) } pub fn main() -> i64 { handle apply(Capability<i64>::relay) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Gate { type Effects<'a, e: EffectRow>: EffectRow; } pub trait Base<T>: Gate { fn relay<'a>(value: &'a i64) -> i64 / { <Self as Gate>::Effects<'a, {}> } where Self: Gate<Effects<'a, {}> = {Trace<i64>}>; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Gate for i64 { type Effects<'a, e: EffectRow> = {Trace<i64>, | e}; } impl Base<i64> for i64 { fn relay<'a>(value: &'a i64) -> i64 / { <i64 as Gate>::Effects<'a, {}> } where i64: Gate<Effects<'a, {}> = {Trace<i64>}> { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl !Top<i64> for i64 {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("negative Top boundary unexpectedly materialized a static method value");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G4169"),
        "missing negative-boundary static method-value rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_materializes_positive_supertrait_hrtb_static_method_values_with_gat_row_equality() {
    // The corresponding positive Top evidence remains a separately proven
    // success case: the GAT equality must normalize under the HRTB rather
    // than making the static method fallback indiscriminately reject it.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn apply(callback: for<'a> (&'a i64) -> i64 / Trace<i64>) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); Trace<i64>::note(result) } pub fn main() -> i64 { handle apply(Capability<i64>::relay) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Gate { type Effects<'a, e: EffectRow>: EffectRow; } pub trait Base<T>: Gate { fn relay<'a>(value: &'a i64) -> i64 / { <Self as Gate>::Effects<'a, {}> } where Self: Gate<Effects<'a, {}> = {Trace<i64>}>; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Gate for i64 { type Effects<'a, e: EffectRow> = {Trace<i64>, | e}; } impl Base<i64> for i64 { fn relay<'a>(value: &'a i64) -> i64 / { <i64 as Gate>::Effects<'a, {}> } where i64: Gate<Effects<'a, {}> = {Trace<i64>}> { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("positive Top GAT-equality static HRTB method value must reach VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_open_rows_from_hrtb_static_method_gat_equalities_through_aliases() {
    // The static method binds both a lifetime and an effect-row generic. Its
    // GAT equality keeps that row open inside `forward`; selection must use
    // the unique Top evidence through the alias without closing `e` early.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::{Gate, Trace}; pub fn forward<e: EffectRow>() -> for<'a> (&'a i64) -> i64 / { <i64 as Gate>::Effects<'a, e> } { Capability<i64>::relay } pub fn apply(callback: for<'a> (&'a i64) -> i64 / Trace<i64>) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); Trace<i64>::note(result) } pub fn main() -> i64 { handle apply(forward<{}>()) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Gate, Top as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Gate { type Effects<'a, e: EffectRow>: EffectRow; } pub trait Base<T>: Gate { fn relay<'a, e: EffectRow>(value: &'a i64) -> i64 / { <Self as Gate>::Effects<'a, e> } where Self: Gate<Effects<'a, e> = {Trace<i64>, | e}>; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Gate for i64 { type Effects<'a, e: EffectRow> = {Trace<i64>, | e}; } impl Base<i64> for i64 { fn relay<'a, e: EffectRow>(value: &'a i64) -> i64 / { <i64 as Gate>::Effects<'a, e> } where i64: Gate<Effects<'a, e> = {Trace<i64>, | e}> { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {} impl !Top<i64> for u64 {}".as_slice(),
    ));
    let first = StageZeroCompiler::new()
        .compile(request.clone())
        .expect("open-row HRTB static method value must retain the GAT equality");
    let second = StageZeroCompiler::new()
        .compile(request)
        .expect("open-row HRTB static method value must materialize deterministically");
    assert!(first.diagnostics.is_empty(), "{:#?}", first.diagnostics);
    assert!(second.diagnostics.is_empty(), "{:#?}", second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 42);
    assert_eq!(second.run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_ambiguous_open_row_hrtb_static_method_values_through_aliases() {
    // The row remains generic while the method value is checked, but the
    // receiver-less extraction still needs one concrete Top dictionary. Two
    // positive subjects prove the same aliased relation, so materialization
    // must stop before it could arbitrarily normalize either GAT row.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Gate; pub fn forward<e: EffectRow>() -> for<'a> (&'a i64) -> i64 / { <i64 as Gate>::Effects<'a, e> } { Capability<i64>::relay } pub fn main() -> i64 { 42 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Gate, Top as Gateway};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub trait Gate { type Effects<'a, e: EffectRow>: EffectRow; } pub trait Base<T>: Gate { fn relay<'a, e: EffectRow>(value: &'a i64) -> i64 / { <Self as Gate>::Effects<'a, e> } where Self: Gate<Effects<'a, e> = {| e}>; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Gate for i64 { type Effects<'a, e: EffectRow> = {| e}; } impl Gate for u64 { type Effects<'a, e: EffectRow> = {| e}; } impl Base<i64> for i64 { fn relay<'a, e: EffectRow>(value: &'a i64) -> i64 / { <i64 as Gate>::Effects<'a, e> } where i64: Gate<Effects<'a, e> = {| e}> { *value } } impl Base<i64> for u64 { fn relay<'a, e: EffectRow>(value: &'a i64) -> i64 / { <u64 as Gate>::Effects<'a, e> } where u64: Gate<Effects<'a, e> = {| e}> { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Middle<i64> for u64 where u64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {} impl Top<i64> for u64 where u64: Middle<i64> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("ambiguous open-row static method value unexpectedly entered VM emission");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G4169"),
        "missing ambiguous open-row static method-value rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_forwards_nested_alias_hrtb_static_methods_with_mixed_row_binders_through_vm() {
    // `relay` has lifetime, type, and effect-row method binders.  The public
    // `Callback` spelling crosses two package aliases, while `relay_to_caller`
    // preserves its still-open row tail before `main` finally closes it.
    let mut request = request(
        "use facade::{Callback, Gate, Gateway as Capability, Trace}; pub fn forward<e: EffectRow>() -> Callback<i64, e> { Capability<i64>::relay } pub fn apply<e: EffectRow>(callback: Callback<i64, e>) -> i64 / {Trace<i64>, | e} { let value = 41; let result = callback(&value, value); Trace<i64>::note(result) } pub fn relay_to_caller<e: EffectRow>() -> i64 / {Trace<i64>, | e} { apply(forward<e>()) } pub fn main() -> i64 { handle relay_to_caller<{}>() { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("facade@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use middle::{First as Gateway, Gate, Trace}; pub type Callback<U, E: EffectRow> = middle::Callback<U, E>;".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("middle@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as First, Gate, Trace}; pub type Callback<U, E: EffectRow> = for<'a> (&'a i64, U) -> i64 / { <i64 as Gate<i64>>::Effects<'a, U, E> };".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Gate<T> { type Effects<'a, U, e: EffectRow>: EffectRow; } pub trait Base<T>: Gate<T> { fn relay<'a, U, e: EffectRow>(value: &'a i64, marker: U) -> i64 / { <Self as Gate<T>>::Effects<'a, U, e> } where Self: Gate<T, Effects<'a, U, e> = {Trace<U>, | e}>; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Gate<i64> for i64 { type Effects<'a, U, e: EffectRow> = {Trace<U>, | e}; } impl Base<i64> for i64 { fn relay<'a, U, e: EffectRow>(value: &'a i64, marker: U) -> i64 / { <i64 as Gate<i64>>::Effects<'a, U, e> } where i64: Gate<i64, Effects<'a, U, e> = {Trace<U>, | e}> { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {} impl !Top<i64> for u64 {}".as_slice(),
    ));
    let first = StageZeroCompiler::new()
        .compile(request.clone())
        .expect("nested aliases must preserve the selected mixed-binder static method value");
    request.sources.reverse();
    let second = StageZeroCompiler::new()
        .compile(request)
        .expect("source ordering must not perturb nested alias materialization");
    assert!(first.diagnostics.is_empty(), "{:#?}", first.diagnostics);
    assert!(second.diagnostics.is_empty(), "{:#?}", second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 42);
    assert_eq!(second.run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_ambiguous_nested_alias_hrtb_static_method_values_with_open_rows() {
    // The two aliases do not hide that two different concrete subjects prove
    // Top<i64>. The generic callback row must not cause static extraction to
    // choose one dictionary merely because both normalize to the same tail.
    let mut request = request(
        "use facade::{Callback, Gate, Gateway as Capability}; pub fn forward<e: EffectRow>() -> Callback<i64, e> { Capability<i64>::relay } pub fn main() -> i64 { 42 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("facade@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use middle::{First as Gateway, Gate, Trace}; pub type Callback<U, E: EffectRow> = middle::Callback<U, E>;".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("middle@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as First, Gate, Trace}; pub type Callback<U, E: EffectRow> = for<'a> (&'a i64, U) -> i64 / { <i64 as Gate<i64>>::Effects<'a, U, E> };".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Gate<T> { type Effects<'a, U, e: EffectRow>: EffectRow; } pub trait Base<T>: Gate<T> { fn relay<'a, U, e: EffectRow>(value: &'a i64, marker: U) -> i64 / { <Self as Gate<T>>::Effects<'a, U, e> } where Self: Gate<T, Effects<'a, U, e> = {| e}>; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Gate<i64> for i64 { type Effects<'a, U, e: EffectRow> = {| e}; } impl Gate<i64> for u64 { type Effects<'a, U, e: EffectRow> = {| e}; } impl Base<i64> for i64 { fn relay<'a, U, e: EffectRow>(value: &'a i64, marker: U) -> i64 / { <i64 as Gate<i64>>::Effects<'a, U, e> } where i64: Gate<i64, Effects<'a, U, e> = {| e}> { *value } } impl Base<i64> for u64 { fn relay<'a, U, e: EffectRow>(value: &'a i64, marker: U) -> i64 / { <u64 as Gate<i64>>::Effects<'a, U, e> } where u64: Gate<i64, Effects<'a, U, e> = {| e}> { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl Middle<i64> for u64 where u64: Base<i64> {} impl Top<i64> for i64 where i64: Middle<i64> {} impl Top<i64> for u64 where u64: Middle<i64> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("ambiguous nested alias static method value unexpectedly entered VM emission");
    };
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        ["G7007", "G4169", "G4182"],
        "unexpected nested-alias ambiguity diagnostics: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_negative_nested_alias_hrtb_static_method_values_with_open_rows() {
    // Negative Top evidence on the only candidate blocks inherited static
    // extraction even though Base and Gate themselves have positive evidence.
    let mut request = request(
        "use facade::{Callback, Gate, Gateway as Capability}; pub fn forward<e: EffectRow>() -> Callback<i64, e> { Capability<i64>::relay } pub fn main() -> i64 { 42 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("facade@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use middle::{First as Gateway, Gate, Trace}; pub type Callback<U, E: EffectRow> = middle::Callback<U, E>;".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("middle@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Top as First, Gate, Trace}; pub type Callback<U, E: EffectRow> = for<'a> (&'a i64, U) -> i64 / { <i64 as Gate<i64>>::Effects<'a, U, E> };".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Gate<T> { type Effects<'a, U, e: EffectRow>: EffectRow; } pub trait Base<T>: Gate<T> { fn relay<'a, U, e: EffectRow>(value: &'a i64, marker: U) -> i64 / { <Self as Gate<T>>::Effects<'a, U, e> } where Self: Gate<T, Effects<'a, U, e> = {| e}>; } pub trait Middle<T>: Base<T> {} pub trait Top<T>: Middle<T> {} impl Gate<i64> for i64 { type Effects<'a, U, e: EffectRow> = {| e}; } impl Base<i64> for i64 { fn relay<'a, U, e: EffectRow>(value: &'a i64, marker: U) -> i64 / { <i64 as Gate<i64>>::Effects<'a, U, e> } where i64: Gate<i64, Effects<'a, U, e> = {| e}> { *value } } impl Middle<i64> for i64 where i64: Base<i64> {} impl !Top<i64> for i64 {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("negative nested alias static method value unexpectedly entered VM emission");
    };
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        ["G7007", "G4169", "G4182"],
        "unexpected negative nested-alias diagnostics: {diagnostics:#?}"
    );
}

#[test]
fn service_selects_aliased_multi_supertrait_hrtb_gat_methods_through_vm() {
    let mut request = request(
        "use bridge::Gateway as Alias; use bridge::Trace; pub fn identity<'a>(value: &'a i64) -> &'a i64 / Trace<i64> { Trace<i64>::note(*value); value } pub fn main() -> i64 { let source = 40; handle Alias<i64>::apply<'static, {}, i64>(&source, identity, 0) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Composite as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Primary<T> { type Item<'a>; type Effects<'a>: EffectRow; fn apply<'z, e: EffectRow, U>(receiver: Self, callback: for<'a> (<Self as Primary<T>>::Item<'a>) -> <Self as Primary<T>>::Item<'a> / { <Self as Primary<T>>::Effects<'a> | e }, marker: U) -> i64 / { <Self as Primary<T>>::Effects<'static> | e }; } pub trait Secondary<T> { type Item<'a>; type Effects<'a>: EffectRow; } pub trait Composite<T>: Primary<T> + Secondary<T> {} impl<'a> Primary<i64> for &'a i64 { type Item<'b> = &'b i64; type Effects<'b> = {Trace<i64>}; fn apply<'z, e: EffectRow, U>(receiver: &'a i64, callback: for<'b> (<&'a i64 as Primary<i64>>::Item<'b>) -> <&'a i64 as Primary<i64>>::Item<'b> / { <&'a i64 as Primary<i64>>::Effects<'b> | e }, marker: U) -> i64 / { <&'a i64 as Primary<i64>>::Effects<'static> | e } { let value = 41; let result = callback(&value); Trace<i64>::note(*receiver); *result + 1 } } impl<'a> Secondary<i64> for &'a i64 { type Item<'b> = &'b i64; type Effects<'b> = {Trace<i64>}; } impl<'a> Composite<i64> for &'a i64 {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("aliased inherited HRTB GAT method must select deterministically");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_aliased_supertrait_gat_effect_obligations_through_vm() {
    // `Gateway` is a public alias for a subtrait whose implementation proves
    // its parent contract through a scoped where-obligation.  Selecting the
    // inherited method must retain the parent GAT and effect-row identities
    // through package aliases all the way to VM handler dispatch.
    let mut request = request(
        "use bridge::Gateway as Capability; use bridge::Trace; pub fn main() -> i64 { let receiver = 0; let value = 41; handle Capability<i64>::relay(&receiver, &value) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Child as Gateway, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<'a>; type Effects<'a>: EffectRow; fn relay<'a>(receiver: Self, value: <Self as Parent<T>>::Item<'a>) -> i64 / { <Self as Parent<T>>::Effects<'a> }; } pub trait Child<T>: Parent<T> {} impl<'r> Parent<i64> for &'r i64 { type Item<'a> = &'a i64; type Effects<'a> = {Trace<i64>}; fn relay<'a>(receiver: &'r i64, value: &'a i64) -> i64 / {Trace<i64>} { Trace<i64>::note(*value) } } impl<'r> Child<i64> for &'r i64 where &'r i64: Parent<i64> {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("aliased scoped supertrait GAT/effect obligations must reach the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_bounds_recursive_aliased_supertrait_gat_obligations_with_negative_evidence() {
    // A parent implementation asks for its subtrait while that same subtrait
    // must establish the parent contract.  The re-exported negative alias
    // makes the recursive fact explicitly impossible.  Interface validation
    // must terminate with coherence and supertrait diagnostics; it must never
    // turn the cycle into synthetic associated GAT/effect-row evidence.
    let mut request = request(
        "use bridge::{Parent as First, Child as Second, DeniedChild}; pub struct Local {} impl First<i64> for Local where Local: Second<i64> { type Item<'a> = &'a i64; type Effects<'a> = {}; } impl Second<i64> for Local {} impl !DeniedChild<i64> for Local {} pub fn main() -> i64 { 42 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Parent, Child, Child as DeniedChild};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub trait Parent<T> { type Item<'a>; type Effects<'a>: EffectRow; } pub trait Child<T>: Parent<T> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("recursive aliased supertrait evidence unexpectedly produced a VM artifact");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G3406"),
        "missing mixed-polarity alias coherence rejection: {diagnostics:#?}"
    );
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G4148"),
        "missing bounded recursive supertrait-obligation rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_executes_alias_equivalent_hrtb_effect_gat_traits_through_vm() {
    let mut request = request(
        "use bridge::First as Primary; use bridge::Second as Secondary; use bridge::Trace; pub fn identity<'a>(value: &'a i64) -> &'a i64 / { <&'a i64 as Secondary<i64>>::Effects<'a> } { Trace<i64>::note(*value); value } pub fn main() -> i64 { let source = 40; handle Primary<i64>::apply<'static, {}, i64>(&source, identity, 0) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Capability as First, Capability as Second, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Capability<T> { type Item<'a>; type Effects<'a>: EffectRow; fn apply<'z, e: EffectRow, U>(receiver: Self, callback: for<'a> (<Self as Capability<T>>::Item<'a>) -> <Self as Capability<T>>::Item<'a> / { <Self as Capability<T>>::Effects<'a> | e }, marker: U) -> i64 / { <Self as Capability<T>>::Effects<'static> | e }; } impl<'r> Capability<i64> for &'r i64 { type Item<'a> = &'a i64; type Effects<'a> = {Trace<i64>}; fn apply<'z, e: EffectRow, U>(receiver: &'r i64, callback: for<'a> (<&'r i64 as Capability<i64>>::Item<'a>) -> <&'r i64 as Capability<i64>>::Item<'a> / { <&'r i64 as Capability<i64>>::Effects<'a> | e }, marker: U) -> i64 / { <&'r i64 as Capability<i64>>::Effects<'static> | e } { let value = 41; let result = callback(&value); Trace<i64>::note(*receiver); *result + 1 } }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("alias-equivalent HRTB GAT trait contracts must materialize");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_cross_trait_hrtb_gat_alias_bounds_through_vm() {
    let mut request = request(
        "use bridge::Left as Primary; use bridge::Right as Secondary; use bridge::Trace; pub fn identity<'a>(value: &'a i64) -> &'a i64 / { <&'a i64 as Secondary<i64>>::Effects<'a> } { Trace<i64>::note(*value); value } pub fn main() -> i64 { let source = 40; handle Primary<i64>::apply<i64>(&source, identity, 0) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{First as Left, Second as Right, Trace};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait First<T> { type Item<'a>; type Effects<'a>: EffectRow; fn apply<U>(receiver: Self, callback: for<'a> (<Self as First<T>>::Item<'a>) -> <Self as First<T>>::Item<'a> / { <Self as First<T>>::Effects<'a> }, marker: U) -> i64 / { <Self as First<T>>::Effects<'static> }; } pub trait Second<T> { type Item<'a>; type Effects<'a>: EffectRow; } impl<'r> First<i64> for &'r i64 { type Item<'a> = <&'r i64 as Second<i64>>::Item<'a>; type Effects<'a> = {Trace<i64>}; fn apply<U>(receiver: &'r i64, callback: for<'a> (<&'r i64 as First<i64>>::Item<'a>) -> <&'r i64 as First<i64>>::Item<'a> / { <&'r i64 as First<i64>>::Effects<'a> }, marker: U) -> i64 / { <&'r i64 as First<i64>>::Effects<'static> } { let value = 41; let result = callback(&value); Trace<i64>::note(*receiver); *result + 1 } } impl<'r> Second<i64> for &'r i64 { type Item<'a> = &'a i64; type Effects<'a> = { <&'r i64 as First<i64>>::Effects<'a> }; }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("cross-trait HRTB GAT aliases must normalize into a VM contract");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_mutually_recursive_hrtb_gat_alias_bounds() {
    let mut request = request(
        "use bridge::Left; pub fn relay<'a>(value: &'a i64) -> &'a i64 / { <&'a i64 as Left<i64>>::Effects<'a> } { value } pub fn main() -> i64 { let value = 40; *relay(&value) + 2 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::First as Left;".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub trait First<T> { type Item<'a>; type Effects<'a>: EffectRow; } pub trait Second<T> { type Item<'a>; type Effects<'a>: EffectRow; } impl<'r> First<i64> for &'r i64 { type Item<'a> = &'a i64; type Effects<'a> = { <&'r i64 as Second<i64>>::Effects<'a> }; } impl<'r> Second<i64> for &'r i64 { type Item<'a> = &'a i64; type Effects<'a> = { <&'r i64 as First<i64>>::Effects<'a> }; }".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("mutually recursive HRTB GAT aliases unexpectedly entered VM emission");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G4155"),
        "missing recursive HRTB GAT rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_alias_equivalent_positive_and_negative_hrtb_gat_impls() {
    let mut request = request(
        "use bridge::First as Positive; use bridge::Second as Negative; pub struct Local {} impl Positive<i64> for Local { type Effects<'a> = {}; } impl !Negative<i64> for Local {} pub fn main() -> i64 { 42 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Capability as First, Capability as Second};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub trait Capability<T> { type Effects<'a>: EffectRow; }".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("alias-equivalent positive and negative implementations coexisted");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G3406"),
        "missing mixed-polarity alias coherence rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_overlapping_impls_spelled_through_trait_reexport_aliases() {
    let mut request = request(
        "use bridge::First as Primary; use bridge::Second as Secondary; pub struct Local {} impl Primary<i64> for Local { type Effects<'a> = {}; } impl Secondary<i64> for Local { type Effects<'a> = {}; } pub fn main() -> i64 { 42 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Capability as First, Capability as Second};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub trait Capability<T> { type Effects<'a>: EffectRow; }".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("two aliases of one trait admitted overlapping implementations");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G3404"),
        "missing alias-equivalent coherence rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_reexported_hrtb_inherited_effect_gats_without_selected_evidence() {
    // The scoped HRTB solver path may open `for<'a>`, but it must not turn the
    // binder itself into evidence.  The public facade exposes the inherited
    // associated row; without a matching `Parent` implementation the root
    // signature remains invalid before any body can reach VM lowering.
    let mut request = request(
        "use bridge::Child; pub fn relay<'a>(value: &'a i64) -> &'a i64 / { <&'a i64 as Child<i64>>::Effects<'a> } { value } pub fn main() -> i64 { 0 }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::Child;".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub trait Parent<T> { type Effects<'a>: EffectRow; } pub trait Child<T>: Parent<T> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("an unselected HRTB associated effect row escaped a dependency facade");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4190"),
        "missing selected-evidence rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_imports_defaulted_associated_gats_for_local_layouts_and_effect_rows() {
    // Interface serialization must retain generic defaults.  The consumer owns
    // the impl heads, omits both associated definitions, and then needs the
    // imported defaults in two independent backend-facing positions: a record
    // field layout and an outward effect row.
    let dependency = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Family { type Item<T> = T; } pub trait Capability { type Effects<T>: EffectRow = {Trace<T>}; }";
    let root = "use dependency::Capability; use dependency::Family; use dependency::Trace; pub struct Value {} impl Family for Value {} impl Capability for Value {} pub struct Packet { value: <Value as Family>::Item<i64> } pub fn worker() -> i64 / { <Value as Capability>::Effects<i64> } { let packet = Packet { value: 41 }; Trace<i64>::note(packet.value) } pub fn main() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(root, "dependency@0.1.0", dependency))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_normalizes_dependency_trait_method_effect_rows_through_handlers() {
    let root = "use dependency::Relay; use dependency::Trace; pub fn apply(callable: (i64) -> i64 / Trace) -> i64 / Trace { callable(0) } pub fn main() -> i64 { handle apply(Relay::relay) { Trace::note() with k => k(42) } }";
    let dependency = "pub effect Trace { note() -> i64; } pub trait Capability { type Effects: EffectRow; } impl Capability for i64 { type Effects = {Trace}; } pub trait Relay { fn relay(receiver: i64) -> i64 / { <i64 as Capability>::Effects }; } impl Relay for i64 { fn relay(receiver: i64) -> i64 / { <i64 as Capability>::Effects } { Trace::note() } }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(
            root,
            "dependency@0.1.0",
            dependency,
        ))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_unselected_associated_effect_rows_on_trait_method_values() {
    let source = "effect Trace { note() -> i64; } trait Capability { type Effects: EffectRow; } trait Relay { fn relay(receiver: i64) -> i64 / { <i64 as Capability>::Effects }; } impl Relay for i64 { fn relay(receiver: i64) -> i64 / { <i64 as Capability>::Effects } { 0 } } pub fn apply(callable: (i64) -> i64 / Trace) -> i64 / Trace { callable(0) } pub fn main() -> i64 { handle apply(Relay::relay) { Trace::note() with k => k(42) } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("an unselected associated effect row escaped through a trait method value");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4190"),
        "missing higher-order associated-effect rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_instantiates_quantity_generic_enum_payloads() {
    let source = "pub enum Packet<q: Quantity, T> { Value(T) } pub fn main() -> i64 { let packet = Packet<[1, 1], i64>::Value(41); 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = "pub enum Packet<q: Quantity, T> { Value(T) } pub fn main() -> i64 { let packet = Packet<[1, 1], i64>::Value(\"wrong\"); 0 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(rejected))
    else {
        panic!("quantity-generic enum payload accepted the wrong value type");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4131"),
        "missing quantity-generic enum payload mismatch diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_materializes_generic_nominal_layouts_with_const_and_quantity_arguments() {
    let source = "pub struct Carrier<n: u32, q: Quantity, T> { value: T } pub fn unpack<n: u32, q: Quantity, T>(value: Carrier<n, q, T>) -> T { value.value } pub fn main() -> i64 { unpack<7, [1, 1], i64>(Carrier<7, [1, 1], i64> { value: 42 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_generic_nominal_layouts_with_associated_const_arguments() {
    let source = "trait First { const Value: u32; } trait Second { const Value: u32; } impl Second for i64 { const Value = 7; } impl First for i64 { const Value = <i64 as Second>::Value; } pub struct Carrier<n: u32, T> { value: T } pub fn unpack<T>(value: Carrier<<T as First>::Value, T>) -> T where T: First { value.value } pub fn main() -> i64 { unpack<i64>(Carrier<7, i64> { value: 42 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_quantity_generic_layouts_with_associated_const_arguments() {
    let source = "trait Budget { const Value: Quantity; } impl Budget for i64 { const Value = [1, 1]; } pub struct Carrier<q: Quantity, T> { value: T } pub fn unpack<T>(value: Carrier<<T as Budget>::Value, T>) -> T where T: Budget { value.value } pub fn main() -> i64 { unpack<i64>(Carrier<[1, 1], i64> { value: 42 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_folds_symbolic_u32_layout_arguments_after_specialization() {
    let source = "pub struct Carrier<n: u32, T> { value: T } pub fn unpack<n: u32>(value: Carrier<n + 1, i64>) -> i64 { value.value } pub fn main() -> i64 { unpack<6>(Carrier<7, i64> { value: 42 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_applies_trailing_const_generic_defaults_to_nominal_layouts() {
    let source = "pub struct Carrier<T, n: u32 = 7> { value: T } pub struct Offset<T, n: u32, m: u32 = n + 1> { value: T } pub struct Budget<T, q: Quantity = [1, 1]> { value: T } pub fn unpack(value: Carrier<i64>) -> i64 { value.value } pub fn offset(value: Offset<i64, 6>) -> i64 { value.value } pub fn budget(value: Budget<i64>) -> i64 { value.value } pub fn main() -> i64 { unpack(Carrier<i64> { value: 20 }) + offset(Offset<i64, 6> { value: 21 }) + budget(Budget<i64> { value: 1 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let non_trailing = "pub struct Broken<T, n: u32 = 7, m: u32> { value: T } pub fn main() -> i64 { 42 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(non_trailing))
    else {
        panic!("a non-trailing structural generic default unexpectedly compiled");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == "G3205"),
        "missing trailing-default diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_lowers_structural_is_patterns_into_verified_vm_tests() {
    let enum_source = "pub enum Result { Ok(i64), Err(Text) } pub fn main() -> Bool { Result::Ok(42) is Result::Ok(42) }";
    let outcome = StageZeroCompiler::new()
        .compile(request(enum_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert!(outcome.artifact.unwrap().run_bool().unwrap());

    let record_source = "pub struct Pair { left: i64, right: Text } pub fn main() -> Bool { Pair { left: 42, right: \"stable\" } is Pair { right: \"stable\", left: 42 } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(record_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert!(outcome.artifact.unwrap().run_bool().unwrap());

    let mismatch_source = "pub enum Result { Ok(i64), Err(Text) } pub fn main() -> Bool { Result::Ok(42) is Result::Ok(7) }";
    let outcome = StageZeroCompiler::new()
        .compile(request(mismatch_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert!(!outcome.artifact.unwrap().run_bool().unwrap());

    let nested_generic_source = "pub struct Pair<T> { left: T, right: T } pub enum Result<T> { Ok(T), Err } pub fn main() -> Bool { Result<Pair<i64>>::Ok(Pair<i64> { left: 1, right: 42 }) is Result<Pair<i64>>::Ok(Pair<i64> { right: 42, left: 1 }) }";
    let outcome = StageZeroCompiler::new()
        .compile(request(nested_generic_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert!(
        outcome.artifact.unwrap().run_bool().unwrap(),
        "nested generic enum/record patterns must retain their field layout proof through the VM"
    );

    let nested_array_source = "pub struct Pair { left: i64, right: i64 } pub enum Result { Ok(Pair), Err } pub fn main() -> Bool { [Result::Ok(Pair { left: 1, right: 42 })] is [Result::Ok(Pair { right: 42, left: 1 })] }";
    let outcome = StageZeroCompiler::new()
        .compile(request(nested_array_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert!(
        outcome.artifact.unwrap().run_bool().unwrap(),
        "nested array/enum/record patterns must lower through the verified VM"
    );

    let array_mismatch_source = "pub fn main() -> Bool { [1, 42] is [1] }";
    let outcome = StageZeroCompiler::new()
        .compile(request(array_mismatch_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert!(
        !outcome.artifact.unwrap().run_bool().unwrap(),
        "array patterns must compare exact length before selecting elements"
    );
}

#[test]
fn service_executes_positive_is_refinements_through_completion_dispatch() {
    let enum_source = "pub enum Result { Ok(i64), Err } pub fn main() -> i64 { handle Result::Ok(42) is Result::Ok(found) { true => found; false => 0 } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(enum_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let negative_source = "pub enum Result { Ok(i64), Err } pub fn main() -> i64 { handle Result::Err is Result::Ok(found) { true => found; false => 42 } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(negative_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let record_source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { handle Pair { left: 1, right: 42 } is Pair { right: selected, left: _ } { true => selected; false => 0 } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(record_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let array_source =
        "pub fn main() -> i64 { handle [1, 42] is [_, found] { true => found; false => 0 } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(array_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(
        outcome.artifact.unwrap().run_i64().unwrap(),
        42,
        "positive array refinements must bind their exact selected element"
    );
}

#[test]
fn service_requires_a_fallback_after_an_exact_array_completion_pattern() {
    let source = "pub fn main() -> i64 { handle [1] { [1] => 1 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("one exact array completion arm unexpectedly proved exhaustive")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4166"),
        "array completion coverage must remain open without a fallback: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_unreachable_nested_array_completion_arm() {
    let source = "pub fn main() -> i64 { handle [[true, false]] { [[true, false]] => 41, [[true, false]] => 42, _ => 0 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("duplicate nested array completion arm unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4168"),
        "duplicate exact array rows must be rejected by ordered completion reachability: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_exact_array_completion_arm_after_a_wildcard() {
    let source = "pub fn main() -> i64 { handle [1] { _ => 0, [1] => 41 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("array arm after an irrefutable wildcard unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4168"),
        "a wildcard must subsume every later exact array row: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_unreachable_nested_array_handler_arm() {
    let source = "effect Ask { [0,1] ask(value: Array<Array<i64>>) -> i64; } pub fn main() -> i64 { handle Ask::ask([[1, 2]]) { Ask::ask([[1, 2]]) => 41, Ask::ask([[1, 2]]) => 42, Ask::ask(_) => 0 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("duplicate nested array handler arm unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4175"),
        "duplicate exact array handler rows must be rejected by shared payload reachability: {diagnostics:#?}"
    );
}

#[test]
fn service_normalizes_concrete_associated_type_arguments_in_nominal_patterns() {
    let source = "trait Element { type Item; } struct Boxed<T> { value: T } impl Element for i64 { type Item = i64; } pub fn main() -> Bool { Boxed { value: 42 } is Boxed<<i64 as Element>::Item> { value: _ } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert!(
        outcome.artifact.unwrap().run_bool().unwrap(),
        "concrete associated type arguments must normalize before nominal pattern identity comparison"
    );
}

#[test]
fn service_rejects_unknown_associated_type_arguments_in_nominal_patterns() {
    let source = "trait Element { type Item; } struct Boxed<T> { value: T } pub fn main() -> Bool { Boxed { value: 42 } is Boxed<<i64 as Element>::Missing> { value: _ } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("unknown associated type in nominal pattern unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4150"),
        "nominal patterns must reject a projection that is absent from the selected trait: {diagnostics:#?}"
    );
}

#[test]
fn service_reports_unsatisfied_associated_type_evidence_in_nominal_patterns() {
    let source = "trait Element { type Item; } struct Boxed<T> { value: T } pub fn main() -> Bool { Boxed { value: 42 } is Boxed<<i64 as Element>::Item> { value: _ } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("nominal pattern with an unsatisfied associated type unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4152"),
        "failed trait evidence must remain distinct from a missing associated item: {diagnostics:#?}"
    );
}

#[test]
fn service_dispatches_nested_array_handler_patterns_through_the_verified_vm() {
    let source = "effect Stop { stop(value: Array<Array<i64>>) -> !; } pub fn main() -> i64 { handle Stop::stop([[1, 2]]) { Stop::stop([[1, 2]]) => 42, Stop::stop(_) => 0 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_checks_effect_operation_identity_and_declared_rows() {
    let accepted = "effect Console { read() -> i64; } pub fn helper() -> i64 / Console { Console::read() } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let missing_row = "effect Console { read() -> i64; } pub fn main() -> i64 { Console::read() }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(missing_row))
    else {
        panic!("undeclared effect performance unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "missing outward-effect diagnostic: {diagnostics:#?}"
    );

    let leaking_call = "effect Console { read() -> i64; } pub fn helper() -> i64 / Console { Console::read() } pub fn main() -> i64 { helper() }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(leaking_call))
    else {
        panic!("effectful direct call escaped through an empty row");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155")
    );
}

#[test]
fn service_executes_a_terminal_handler_without_leaking_an_unhandled_effect() {
    let source = "effect Stop { stop() -> !; } pub fn main() -> i64 { handle { Stop::stop() } { Stop::stop() => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_propagates_terminal_operations_through_strict_expression_contexts() {
    let source = "effect Stop { stop() -> !; } struct Packet { value: i64 } pub fn consume(value: i64) -> i64 { value } pub fn through_block() -> i64 { handle { 0; Stop::stop(); 1 } { Stop::stop() => 40 } } pub fn through_tuple() -> i64 { handle (Stop::stop(), 1) { Stop::stop() => 1 } } pub fn through_array() -> i64 { handle [Stop::stop()] { Stop::stop() => 1 } } pub fn through_record() -> i64 { handle Packet { value: Stop::stop() } { Stop::stop() => 0 } } pub fn through_call() -> i64 { handle consume(Stop::stop()) { Stop::stop() => 0 } } pub fn main() -> i64 { through_block() + through_tuple() + through_array() + through_record() + through_call() }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_discards_unreachable_ownership_effects_after_terminal_strict_operands() {
    // The second tuple operand is well-typed but would create a unique loan
    // and then illegally move its referent if it ever executed. `stop` is the
    // left-to-right first operand and never completes, so neither PlaceFlow
    // nor MIR may manufacture the later move/cleanup state.
    let source = "effect Stop { stop() -> !; } pub fn main() -> i64 { let value = 7; handle (Stop::stop(), { let loan = &mut value; move value }) { Stop::stop() => 42 } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("unreachable ownership suffix must not reject the terminal path");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(
        outcome.artifact.unwrap().run_i64().unwrap(),
        42,
        "the VM must execute only the terminal handler path, not the unreachable ownership suffix"
    );
}

#[test]
fn service_binds_terminal_handler_payloads_before_executing_the_clause() {
    let source = "effect Stop { stop(value: i64) -> !; } pub fn main() -> i64 { handle Stop::stop(42) { Stop::stop(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_terminal_handlers_for_the_exact_generic_effect_instance() {
    let source = "effect Fail<E> { fail(error: E) -> !; } pub fn main() -> i64 { handle Fail<i64>::fail(42) { Fail<i64>::fail(error) => error } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_dispatches_terminal_handler_patterns_through_verified_cfg() {
    let source = "effect Stop { stop(value: i64) -> !; } pub fn choose(value: i64) -> i64 { handle Stop::stop(value) { Stop::stop(1) => 41, Stop::stop(other) => other } } pub fn main() -> i64 { choose(1) + choose(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn service_dispatches_structural_terminal_handler_patterns_through_verified_cfg() {
    let source = "pub enum Choice { Left, Right } effect Stop { stop(value: Choice) -> !; } pub fn choose(value: Choice) -> i64 { handle Stop::stop(value) { Stop::stop(Choice::Left) => 41, Stop::stop(_) => 42 } } pub fn main() -> i64 { choose(Choice::Left) + choose(Choice::Right) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn service_proves_enum_operation_coverage_without_an_irrefutable_catch_all() {
    let source = "pub enum Choice { Left, Right } effect Ask { ask(value: Choice) -> i64; } pub fn main() -> i64 { handle Ask::ask(Choice::Left) { Ask::ask(Choice::Left) => 41, Ask::ask(Choice::Right) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_bool_operation_coverage_without_an_irrefutable_catch_all() {
    let source = "effect Ask { ask(value: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(true) { Ask::ask(true) => 41, Ask::ask(false) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_multi_argument_bool_operation_coverage_without_a_catch_all() {
    let source = "effect Ask { ask(left: Bool, right: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(true, false) { Ask::ask(true, _) => 41, Ask::ask(false, _) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_mixed_enum_and_bool_operation_coverage_without_a_catch_all() {
    let source = "pub enum Choice { Left, Right } effect Ask { ask(choice: Choice, enabled: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(Choice::Left, false) { Ask::ask(Choice::Left, _) => 41, Ask::ask(Choice::Right, _) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_keeps_a_partial_finite_operation_in_the_outward_effect_row() {
    let source = "effect Ask { ask(value: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(false) { Ask::ask(true) => 41 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("partial Bool handler unexpectedly compiled as closed");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155")
    );
}

#[test]
fn service_keeps_a_partial_multi_argument_bool_matrix_in_the_outward_effect_row() {
    let source = "effect Ask { ask(left: Bool, right: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(true, false) { Ask::ask(true, true) => 41, Ask::ask(false, false) => 42 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("partial Bool matrix unexpectedly compiled as closed");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155")
    );
}

#[test]
fn service_dispatches_record_terminal_handler_patterns_through_verified_cfg() {
    let source = "pub struct Ticket { serial: i64 } effect Stop { stop(value: Ticket) -> !; } pub fn choose(value: Ticket) -> i64 { handle Stop::stop(value) { Stop::stop(Ticket { serial: 41 }) => 1, Stop::stop(_) => 2 } } pub fn main() -> i64 { choose(Ticket { serial: 41 }) + choose(Ticket { serial: 42 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 3);
}

#[test]
fn service_projects_nested_record_binders_in_a_terminal_handler_arm() {
    let source = "pub struct Ticket { serial: i64 } effect Stop { stop(value: Ticket) -> !; } pub fn choose(value: Ticket) -> i64 { handle Stop::stop(value) { Stop::stop(Ticket { serial: serial }) => serial } } pub fn main() -> i64 { choose(Ticket { serial: 42 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_projects_nested_enum_binders_in_a_terminal_handler_arm() {
    let source = "pub enum Ticket { Number(i64), Empty } effect Stop { stop(value: Ticket) -> !; } pub fn choose(value: Ticket) -> i64 { handle Stop::stop(value) { Stop::stop(Ticket::Number(serial)) => serial, Stop::stop(_) => 0 } } pub fn main() -> i64 { choose(Ticket::Number(42)) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_projects_tuple_binders_in_a_terminal_handler_arm() {
    let source = "effect Stop { stop(pair: (i64, i64)) -> !; } pub fn choose(pair: (i64, i64)) -> i64 { handle Stop::stop(pair) { Stop::stop((left, right)) => left + right } } pub fn main() -> i64 { choose((40, 2)) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_requires_all_terminal_handler_payload_patterns_before_selecting_an_arm() {
    let source = "effect Stop { stop(left: i64, right: i64) -> !; } pub fn choose(left: i64, right: i64) -> i64 { handle Stop::stop(left, right) { Stop::stop(1, 2) => 41, Stop::stop(first, second) => first + second } } pub fn main() -> i64 { choose(1, 2) + choose(3, 4) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 48);
}

#[test]
fn service_executes_a_direct_one_shot_resumption_at_the_handler_root() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_an_aliased_one_shot_resumption_with_vm_parity() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let answer = Ask::ask(); answer + 1 } { Ask::ask() with k => { let saved = k; saved(41) } } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_residual_effects_through_an_aliased_resumption_snapshot() {
    // `saved` is a first-class continuation whose callable type has the
    // residual `Log` effect row. The inner handler must not erase that row
    // merely because the continuation is captured before it is resumed.
    let source = "effect Ask { [1,1] ask() -> i64; } effect Log { [1,1] log(value: i64) -> i64; } pub fn relay() -> i64 / Log { handle { let answer = Ask::ask(); Log::log(answer) } { Ask::ask() with k => { let saved = k; saved(41) } } } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumes_an_aliased_inner_snapshot_into_an_outer_effect_handler() {
    // The inner `Ask` continuation retains `Log` as an outward effect. Its
    // aliased snapshot must restore the inner frame before `Log` is
    // dispatched to the enclosing handler; that outer resumption then
    // restores the inner cleanup path before the result returns.
    let source = "effect Ask { [1,1] ask() -> i64; } effect Log { [1,1] log(value: i64) -> i64; } pub fn main() -> i64 { handle { handle { let answer = Ask::ask(); Log::log(answer) } { Ask::ask() with k => { let saved = k; saved(41) } } } { Log::log(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_restores_three_nested_handler_frames_for_aliased_residual_resumptions() {
    // Each resumption restores the frames outside the operation it handles:
    // Ask resumes into Log while Ask remains above Log, then Log resumes into
    // Audit while both inner frames remain above Audit. The result exercises
    // deep frame restoration plus the ordinary reverse uninstall path.
    let source = "effect Ask { [1,1] ask() -> i64; } effect Log { [1,1] log(value: i64) -> i64; } effect Audit { [1,1] audit(value: i64) -> i64; } pub fn main() -> i64 { handle { handle { handle { let asked = Ask::ask(); let logged = Log::log(asked); Audit::audit(logged) } { Ask::ask() with k => { let saved = k; saved(40) } } } { Log::log(value) with k => { let saved = k; saved(value + 1) } } } { Audit::audit(value) with k => { let saved = k; saved(value + 1) } } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_dispatches_a_pattern_matrix_inside_a_three_deep_residual_handler_stack() {
    // The first Log row declines its literal pattern, so dispatch must reach
    // the later payload-binding row without losing the Ask and Audit frame
    // suffixes restored by the aliased continuations.
    let source = "effect Ask { [1,1] ask() -> i64; } effect Log { [1,1] log(value: i64) -> i64; } effect Audit { [1,1] audit(value: i64) -> i64; } pub fn main() -> i64 { handle { handle { handle { let asked = Ask::ask(); let logged = Log::log(asked); Audit::audit(logged) } { Ask::ask() with k => { let saved = k; saved(40) } } } { Log::log(0) with k => { let saved = k; saved(0) }; Log::log(value) with k => { let saved = k; saved(value + 1) } } } { Audit::audit(value) with k => { let saved = k; saved(value + 1) } } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_replays_a_three_deep_residual_handler_stack_with_cloned_frame_suffixes() {
    // Each `Ask` replay restores fresh Log/Audit frame suffixes. The two
    // residual paths produce 22 and 23 respectively, and the replay clause
    // observes both `ResumeReturn` results before cancelling its exact-[2,2]
    // frame.
    let source = "effect Ask { [2,2] ask() -> i64; } effect Log { [1,1] log(value: i64) -> i64; } effect Audit { [1,1] audit(value: i64) -> i64; } pub fn main() -> i64 { handle { handle { handle { let asked = Ask::ask(); let logged = Log::log(asked); Audit::audit(logged) } { Ask::ask() with k => k(20) + k(21) } } { Log::log(value) with k => k(value + 1) } } { Audit::audit(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 45);
}

#[test]
fn service_keeps_a_statement_handler_alias_closed_before_later_shadowing() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => { let saved = k; saved(41) } }; let saved = (value: i64) -> i64 { value + 1 }; saved(41) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumes_statement_handler_residual_before_outer_suffix() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let answer = Ask::ask(); answer + 1 } { Ask::ask() with k => k(41) }; let saved = (value: i64) -> i64 { value + 1 }; saved(41) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_restores_statement_handler_residual_through_an_aliased_snapshot() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let answer = Ask::ask(); answer + 1 } { Ask::ask() with k => { let saved = k; saved(41) } }; 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_dispatches_refutable_statement_handler_clauses_before_outer_suffix() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask(2) { Ask::ask(1) with k => k(40), Ask::ask(seed) with k => k(seed + 40) }; 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_cancels_an_affine_statement_handler_before_outer_suffix() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(_) => 41 }; 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_cancels_a_nested_affine_handler_without_reentering_the_outer_frame() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { handle Ask::ask() { Ask::ask(_) => 40 } } { Ask::ask(_) => 41 }; 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_nested_statement_handler_before_outer_suffix() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(40) { Ask::ask(0) with k => k(0) } } { Ask::ask(value) with k => k(value + 2) }; 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_composes_a_direct_operation_arm_with_a_normal_completion_arm() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { value => value + 1, Ask::ask() => 41 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_composes_full_control_operation_dispatch_with_normal_completion() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask(1) { value => value + 1, Ask::ask(1, k) => k(41), Ask::ask(_, k) => k(0) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_mixed_handler_uses_explicit_trap_miss_for_finite_operation_coverage() {
    let source = "effect Ask { [1,1] ask(value: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(true) { value => value, Ask::ask(true) => 41, Ask::ask(false) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_preserves_setup_before_a_mixed_direct_handler_operation() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle { let seed = 41; Ask::ask(seed) } { value => value + 1, Ask::ask(payload) => payload } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_terminal_operation_arms_bypass_normal_completion() {
    let source = "effect Stop { stop() -> !; } pub fn main() -> i64 { handle Stop::stop() { value => value, Stop::stop() => 41 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_discarded_operation_arms_bypass_normal_completion() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { value => value + 1, Ask::ask(_) => 41 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_mixed_resumptive_and_discarded_arms_take_distinct_completion_paths() {
    let source = "effect Ask { [0,1] ask(value: Bool) -> i64; } pub fn choose(value: Bool) -> i64 { handle Ask::ask(value) { result => result + 1, Ask::ask(true) => 41, Ask::ask(false, _) => 7 } } pub fn main() -> i64 { choose(true) + choose(false) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 49);
}

#[test]
fn service_runs_completion_for_a_pure_computation_inside_an_operation_handler() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle 41 { value => value + 1, Ask::ask() => 0 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_effect_free_calls_inside_an_unexercised_handler_scope() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn identity(value: i64) -> i64 { value } pub fn main() -> i64 { handle identity(41) { value => value + 1, Ask::ask() => 0 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_normalizes_resume_migration_syntax_to_the_same_direct_resumption() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => resume(k, 42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_normalizes_legacy_perform_and_with_migration_syntax_through_vm_handlers() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle perform Ask::ask() { Ask::ask() with k => resume(k, 42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_the_pattern_slot_full_control_handler_form() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_allows_an_affine_pattern_slot_continuation_to_be_discarded() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(_) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_discard_of_a_required_pattern_slot_continuation() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(_) => 42 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("required continuation discard unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4160")
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5012"),
        "missing declarative cancellation quantity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_dispatches_direct_resumptions_after_pattern_selection() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn choose(value: i64) -> i64 { handle Ask::ask(value) { Ask::ask(1) with k => k(41), Ask::ask(_) with k => resume(k, 42) } } pub fn main() -> i64 { choose(1) + choose(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn service_tail_resumes_a_direct_resumptive_operation_with_the_clause_value() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_enters_a_nonempty_let_bound_continuation_via_a_cfg_parameter() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask() with k => k(41) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_affine_discard_bypasses_a_nonempty_residual_continuation() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask(_) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_uses_complete_enum_coverage_without_a_catch_all() {
    let source = "pub enum Choice { Left, Right } effect Ask { [1,1] ask(value: Choice) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(Choice::Left); value + 1 } { Ask::ask(Choice::Left, k) => k(41), Ask::ask(Choice::Right, k) => k(0) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_preserves_pure_setup_before_the_intercepted_operation() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let seed = 40; let value = Ask::ask(seed); value + 1 } { Ask::ask(payload) with k => k(payload) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_resumption_preserves_pure_setup_before_the_root_handler() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { let seed = 41; handle { let value = Ask::ask(seed); value + 1 } { Ask::ask(payload) with k => k(payload) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_reinstalls_static_dispatch_for_a_second_linear_performance() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let left = Ask::ask(20); let right = Ask::ask(21); left + right } { Ask::ask(payload) with k => k(payload) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_resumption_reuses_ordered_pattern_dispatch_at_each_linear_performance() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let left = Ask::ask(1); let right = Ask::ask(2); left + right } { Ask::ask(1) with k => k(40); Ask::ask(_) with k => k(2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_linear_resumption_uses_complete_bool_coverage_without_a_catch_all() {
    let source = "effect Ask { [1,1] ask(value: Bool) -> i64; } pub fn main() -> i64 { handle { let left = Ask::ask(true); let right = Ask::ask(false); left + right } { Ask::ask(true, k) => k(40), Ask::ask(false, k) => k(2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_affine_discard_exits_a_linear_handler_before_later_performances() {
    let source = "effect Ask { [0,1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle { let left = Ask::ask(1); let right = Ask::ask(2); left + right } { Ask::ask(1, _) => 42, Ask::ask(_, k) => k(0) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_dispatches_each_operation_identity_in_a_linear_handler() {
    let source = "effect Pair { [1,1] first() -> i64; [1,1] second() -> i64; } pub fn main() -> i64 { handle { let left = Pair::first(); let right = Pair::second(); left + right } { Pair::first() with k => k(40); Pair::second() with k => k(2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_an_irrefutable_normal_completion_arm() {
    let source = "pub fn main() -> i64 { handle 41 { value => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_uses_the_implicit_identity_normal_completion_arm() {
    let source = "pub fn main() -> i64 { handle 42 {} }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_a_wildcard_normal_completion_arm() {
    let source = "pub fn main() -> i64 { handle 41 { _ => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_dispatches_ordered_literal_normal_completion_arms_through_verified_cfg() {
    let source = "pub fn choose(value: i64) -> i64 { handle value { 1 => 41, _ => 42 } } pub fn main() -> i64 { choose(1) + choose(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn service_binds_tuple_values_in_a_normal_completion_arm() {
    let source = "pub fn main() -> i64 { handle (40, 2) { (left, right) => left + right } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_classifies_qualified_enum_constructor_arms_as_completion_patterns() {
    let source = "pub enum Choice { Left, Right } pub fn main() -> i64 { handle Choice::Left { Choice::Left => 41, _ => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_classifies_record_completion_arms_before_effect_operation_syntax() {
    let source = "pub struct Ticket { serial: i64 } pub fn main() -> i64 { handle Ticket { serial: 41 } { Ticket { serial: 41 } => 41, _ => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_enum_normal_completion_coverage_without_a_wildcard() {
    let source = "pub enum Choice { Left, Right } pub fn main() -> i64 { handle Choice::Right { Choice::Left => 41, Choice::Right => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_proves_enum_constructor_coverage_with_unbounded_payloads() {
    let completion = "pub enum Result { Ok(i64), Err(Text) } pub fn main() -> i64 { handle Result::Ok(41) { Result::Ok(_) => 41, Result::Err(_) => 42 } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(completion))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);

    // The same constructor-total proof discharges a handled operation. MIR
    // still retains the structural patterns and the verified VM selects the
    // matching payload row at runtime.
    let handler = "pub enum Result { Ok(i64), Err(Text) } effect Inspect { [1, 1] inspect(value: Result) -> i64; } pub fn worker(value: Result) -> i64 / Inspect { Inspect::inspect(value) } pub fn main() -> i64 { handle worker(Result::Ok(41)) { Inspect::inspect(Result::Ok(_)) => 41, Inspect::inspect(Result::Err(_)) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(handler)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);

    // Unbounded sibling payloads remain safe when every row treats them
    // irrefutably; the symbolic proof partitions only the enum column.
    let multi_payload = "pub enum Result { Ok(i64), Err(Text) } effect Inspect { [1, 1] inspect(value: Result, context: i64) -> i64; } pub fn worker(value: Result, context: i64) -> i64 / Inspect { Inspect::inspect(value, context) } pub fn main() -> i64 { handle worker(Result::Ok(41), 7) { Inspect::inspect(Result::Ok(_), _) => 41, Inspect::inspect(Result::Err(_), _) => 42 } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(multi_payload))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_allows_tuple_enum_patterns_to_omit_a_discardable_payload_suffix() {
    // The omitted second payload is an opaque discard. This is intentionally
    // source-to-VM: the shared pattern decision must retain the real enum
    // arity while projecting only the source-selected prefix.
    let source = "pub enum Pair { Both(i64, i64), None } pub fn main() -> i64 { handle Pair::Both(41, 2) { Pair::Both(left) => left + 1, Pair::None => 0 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_tuple_enum_patterns_with_excess_payloads() {
    let source = "pub enum Single { Value(i64) } pub fn main() -> i64 { handle Single::Value(1) { Single::Value(1, 2) => 41, _ => 42 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("tuple enum pattern with too many payloads unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4214"),
        "missing tuple enum payload-arity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_omitting_a_required_use_tuple_enum_payload() {
    let source = "pub struct Ticket { marker: i64 } impl Use<[1, 1]> for Ticket {} pub enum Pair { Both(i64, Ticket), None } pub fn main() -> i64 { handle Pair::Both(41, Ticket { marker: 0 }) { Pair::Both(left) => left + 1, Pair::None => 0 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("omitting a must-use enum payload unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4219"),
        "missing zero-use discard diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_does_not_treat_a_refined_unbounded_enum_constructor_as_total() {
    let source = "pub enum Result { Ok(Bool), Err(i64) } pub fn main() -> i64 { handle Result::Ok(true) { Result::Ok(true) => 41, Result::Err(_) => 42 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("a partially covered constructor unexpectedly proved exhaustive");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4166"),
        "constructor coverage must require an irrefutable payload row: {diagnostics:#?}"
    );
}

#[test]
fn service_proves_bool_normal_completion_coverage_without_a_wildcard() {
    let source = "pub fn main() -> i64 { handle false { true => 41, false => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_proves_nested_enum_payload_coverage_without_a_wildcard() {
    let source = "pub enum Bit { Zero, One } pub enum Packet { Data(Bit), End } pub fn main() -> i64 { handle Packet::Data(Bit::One) { Packet::Data(Bit::Zero) => 40, Packet::Data(Bit::One) => 41, Packet::End => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_nested_tuple_bool_coverage_without_a_wildcard() {
    let source = "pub fn main() -> i64 { handle (true, false) { (true, true) => 40, (true, false) => 41, (false, true) => 42, (false, false) => 43 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_record_field_coverage_without_a_wildcard() {
    let source = "pub struct Flagged { value: Bool } pub fn main() -> i64 { handle Flagged { value: false } { Flagged { value: true } => 40, Flagged { value: false } => 41 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_rejects_an_unreachable_nested_completion_arm() {
    let source = "pub enum Bit { Zero, One } pub enum Packet { Data(Bit), End } pub fn main() -> i64 { handle Packet::Data(Bit::One) { Packet::Data(Bit::Zero) => 40, Packet::Data(Bit::One) => 41, Packet::Data(Bit::One) => 42, Packet::End => 43 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("unreachable completion arm unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4168"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_discharges_an_effect_through_nested_payload_coverage() {
    let source = "pub enum Bit { Zero, One } pub enum Packet { Data(Bit), End } effect Inspect { [1,1] inspect(value: Packet) -> i64; } pub fn worker(value: Packet) -> i64 / Inspect { Inspect::inspect(value) } pub fn main() -> i64 { handle worker(Packet::Data(Bit::One)) { Inspect::inspect(Packet::Data(Bit::Zero)) => 40, Inspect::inspect(Packet::Data(Bit::One)) => 41, Inspect::inspect(Packet::End) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_rejects_partial_normal_completion_coverage_without_a_fallback() {
    let source = "pub fn main() -> i64 { handle false { true => 41 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("partial completion handler unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4166")
    );
}

#[test]
fn service_tail_resumption_enters_the_same_nonempty_continuation() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask() => 41 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_a_direct_one_shot_handler_through_vm_handler_frames() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask(41) { Ask::ask(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_a_nested_partial_one_shot_handler_through_vm_frames() {
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Choice::second(40) { Choice::first(seed) => seed } } { Choice::second(seed) => seed + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_through_an_arbitrary_depth_one_shot_handler_chain() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { handle { handle Ask::ask(40) { Ask::ask(0) with k => k(0) } } { Ask::ask(1) with k => k(1) } } { Ask::ask(2) with k => k(2) } } { Ask::ask(value) with k => k(value + 2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. }))
            .count(),
        4
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::Forward))
            .count(),
        3
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_tries_ordered_refutable_clauses_at_every_deep_one_shot_handler_layer() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { handle Ask::ask(40) { Ask::ask(0) with k => k(0), Ask::ask(2) with k => k(2) } } { Ask::ask(0) with k => k(0), Ask::ask(1) with k => k(1) } } { Ask::ask(0) with k => k(0), Ask::ask(value) with k => k(value + 2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. }))
            .count(),
        3
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::Forward))
            .count(),
        2
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_specializes_refutable_direct_dispatch_with_multiple_sibling_groups() {
    let source = "effect Choice { [1,1] direct(seed: i64) -> i64; [1,1] alpha(seed: i64) -> i64; [1,1] beta(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Choice::direct(40) { Choice::direct(0) with k => k(0), Choice::direct(1) with k => k(1), Choice::alpha(0) with k => k(0), Choice::beta(seed) with k => k(seed) } } { Choice::direct(seed) with k => k(seed + 2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. }))
            .count(),
        4
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Forward))
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_lexical_setup_at_every_deep_one_shot_handler_layer() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let outer_seed = 40; handle { let middle_seed = outer_seed; handle { let inner_seed = middle_seed; Ask::ask(inner_seed) } { Ask::ask(0) with k => k(0) } } { Ask::ask(1) with k => k(1) } } { Ask::ask(value) with k => k(value + 2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. }))
            .count(),
        3
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_a_refutable_inner_one_shot_clause_to_an_outer_frame() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(40) { Ask::ask(0) => 0 } } { Ask::ask(seed) => seed + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_a_refutable_generic_effect_clause_to_the_matching_outer_instance() {
    let source = "effect State<T> { [1,1] set(value: T) -> T; } pub fn main() -> i64 { handle { handle State<i64>::set(40) { State<i64>::set(0) => 0 } } { State<i64>::set(value) => value + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_tries_ordered_refutable_one_shot_clauses_before_forwarding() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(40) { Ask::ask(0) => 0, Ask::ask(40) => 42 } } { Ask::ask(seed) => seed + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_uses_an_irrefutable_inner_fallback_before_the_outer_handler() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(40) { Ask::ask(0) => 0, Ask::ask(seed) => seed + 2 } } { Ask::ask(seed) => seed + 10 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_keeps_nested_handler_setup_inside_its_outer_frame_scope() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let seed = 40; handle Ask::ask(seed) { Ask::ask(0) => 0 } } { Ask::ask(value) => value + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_keeps_inner_computation_setup_inside_its_inner_frame_scope() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { let seed = 40; Ask::ask(seed) } { Ask::ask(0) => 0 } } { Ask::ask(value) => value + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_installs_sibling_operation_frames_for_nested_handler_setup() {
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { let first = Choice::first(40); Choice::second(first) } { Choice::first(value) => value + 1, Choice::second(0) => 0 } } { Choice::second(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_installs_distinct_sibling_operation_frames_for_nested_handler_setup() {
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; [1,1] third(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { let first = Choice::first(40); let second = Choice::second(first); Choice::third(second) } { Choice::first(value) => value + 1, Choice::second(value) => value + 1, Choice::third(value) => value } } { Choice::third(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_uses_ordered_refutable_clauses_for_distinct_sibling_operation_frames() {
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; [1,1] third(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { let first = Choice::first(40); let second = Choice::second(first); Choice::third(second) } { Choice::first(0) => 0, Choice::first(value) => value + 1, Choice::second(value) => value + 1, Choice::third(value) => value } } { Choice::third(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_uses_ordered_sibling_handler_clauses_during_nested_setup() {
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { let first = Choice::first(40); Choice::second(first) } { Choice::first(0) => 0, Choice::first(value) => value + 1, Choice::second(0) => 0 } } { Choice::second(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_a_generic_effect_handler_through_vm_frames() {
    let source = "effect State<T> { [1,1] get() -> T; } pub fn main() -> i64 { handle State<i64>::get() { State<i64>::get() => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_matches_effect_row_generic_instances_in_vm_handler_frames() {
    // The row argument is part of the nominal protocol identity.  It must
    // survive elaboration, handler installation, bytecode encoding, and
    // runtime dispatch rather than being erased as callable-only metadata.
    let source = "effect Trace { note() -> i64; } effect Relay<e: EffectRow> { [1,1] relay(value: i64) -> i64; } pub fn main() -> i64 { handle Relay<{Trace}>::relay(41) { Relay<{Trace}>::relay(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(entry.instructions.iter().any(|instruction| matches!(
        instruction,
        VmInstruction::InstallHandler {
            effect_arguments,
            ..
        } if matches!(effect_arguments.as_slice(), [VmGenericArgument::EffectRow(row)] if row.effects.len() == 1 && row.projections.is_empty() && row.tail.is_none())
    )));
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_an_effect_row_generic_function_value_through_a_vm_handler() {
    let source = "effect Trace { [1,1] note() -> i64; } pub fn leaf() -> i64 / Trace { Trace::note() } pub fn forward<e: EffectRow>(call: () -> i64 / {| e}) -> i64 / {| e} { call() } pub fn main() -> i64 { handle forward<{Trace}>(leaf) { Trace::note() with k => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_instantiates_generic_effect_operations_at_the_call_and_handler() {
    let source = "effect Ask { ask<T>(value: T) -> T; } pub fn main() -> i64 { handle Ask::ask<i64>(41) { Ask::ask<i64>(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_infers_generic_effect_operation_arguments_at_the_call_and_handler() {
    let source = "effect Ask { ask<T>(value: T) -> T; } pub fn main() -> i64 { handle Ask::ask(41) { Ask::ask(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_keeps_protocol_and_operation_generic_arguments_in_distinct_slots() {
    let source = "effect State<T> { replace<U>(value: T, replacement: U) -> U; } pub fn main() -> Text { handle State<i64>::replace<Text>(0, \"selected\") { State<i64>::replace<Text>(value, replacement) => replacement } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_text().unwrap(), "selected");
}

#[test]
fn service_preserves_mixed_effect_operation_generics_at_perform_and_handler() {
    let source = "effect Pulse { stop<'a, e: EffectRow, n: u32, q: Quantity>() -> !; } pub fn main() -> i64 { handle Pulse::stop<'static, {}, 7, [1, 1]>() { Pulse::stop<'static, {}, 7, [1, 1]>() => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_wrong_generic_effect_operation_arity() {
    let source = "effect Ask { ask<T>(value: T) -> T; } pub fn main() -> i64 { handle Ask::ask<i64, Text>(41) { Ask::ask<i64>(value) => value + 1 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("wrong operation generic arity unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4152"),
        "missing generic operation arity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_source_self_application_without_recursive_inference() {
    let source = "pub fn main() -> i64 { let self_apply = { value => value(value) }; 0 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("self application unexpectedly formed an executable recursive callable type")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4105"),
        "self application must fail structurally before any recursive inference can escape: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_an_omitted_const_callable_argument_without_constraints() {
    let source =
        "pub fn unconstrained<n: u32>() -> i64 { 42 } pub fn main() -> i64 { unconstrained() }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("unconstrained omitted const generic unexpectedly reached executable Core");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4116"),
        "missing unresolved const-inference diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_a_direct_one_resume_lowering_for_an_exact_two_shot_contract() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => k(42) } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("single direct resume unexpectedly satisfied a two-shot contract");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6005"),
        "missing direct-resumption quantity diagnostic: {diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5012"),
        "missing structured continuation-use diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_executes_every_exact_finite_direct_resumption() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => k(20) + k(22) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_replays_a_pure_nonempty_finite_resumption_per_explicit_use() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask(k) => k(20) + k(21) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_replays_the_full_pure_residual_prefix_per_finite_resumption() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); let bumped = value + 1; bumped * 2 } { Ask::ask(k) => k(20) + k(21) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 86);
}

#[test]
fn service_replays_each_finite_resumption_through_deep_normal_completion() {
    // A replay restores the whole deep delimiter, not just the suspended
    // computation.  Each resumed path must therefore enter the normal
    // completion matrix before returning to the operation clause: (20 + 1)
    // and (21 + 1) are independently doubled, then observed by the clause.
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { let factor = 2; handle { let value = Ask::ask(); value + 1 } { value => value * factor, Ask::ask() with k => k(20) + k(21) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 86);
}

#[test]
fn service_dispatches_ordered_finite_resumption_patterns_before_replay() {
    let source = "effect Ask { [2,2] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(2); value + 1 } { Ask::ask(1) with k => k(10) + k(11), Ask::ask(seed) with k => k(seed * 10) + k(seed * 11) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 44);
}

#[test]
fn service_selects_the_first_matching_finite_resumption_clause() {
    let source = "effect Ask { [2,2] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(1); value + 1 } { Ask::ask(1) with k => k(20) + k(21), Ask::ask(seed) with k => k(seed * 10) + k(seed * 11) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_rejects_deferred_resumption_quantities_at_the_g1_source_boundary() {
    // Section 10.1 of the branded-environment core specification deliberately
    // limits source resumptions to `[0,1]` and exact finite `[n,n]` while
    // branch-sensitive lower/upper-bound accounting remains deferred.  The
    // quantity and bytecode representations may be general, but accepting
    // `[1,2]` at this boundary would promise a source semantic the compiler
    // has not specified how to prove on every path.
    for quantity in ["[1,2]", "[0,2]", "[1,infinity]"] {
        let source = format!(
            "effect Ask {{ {quantity} ask() -> i64; }} pub fn main() -> i64 {{ handle Ask::ask() {{ Ask::ask(k) => k(41) }} }}"
        );
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
            StageZeroCompiler::new().compile(request(&source))
        else {
            panic!("the unsupported {quantity} resumption quantity unexpectedly compiled");
        };
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G3254"),
            "missing source-boundary resumption-quantity diagnostic for {quantity}: {diagnostics:#?}"
        );
    }
}

#[test]
fn service_reenters_a_dynamic_replayable_handler_clause_per_resume() {
    // Assignment keeps the residual off the pure Core replayer, so this
    // exercises the VM replay frame and its clause-return edge instead.
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); let mutable = value; mutable = mutable + 1; mutable } { Ask::ask(k) => k(20) + k(21) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_reinstates_an_outer_finite_handler_across_a_nested_dynamic_suspension() {
    let source = "effect Ops { [2,2] outer() -> i64; [1,1] inner() -> i64; } pub fn main() -> i64 { handle { handle Ops::outer() { Ops::inner(k) => k(40) } } { Ops::outer(k) => k(20) + k(22) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumes_an_outer_handler_from_a_nested_handler_arm() {
    let source = "effect Ask { [1,1] ask() -> i64; } effect Ping { [1,1] ping() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with outer => handle Ping::ping() { Ping::ping() with inner => { let value = inner(41); outer(value) } } } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 41);
}

#[test]
fn service_preserves_inner_clause_setup_and_residual_before_outer_resumption() {
    // The inner arm has ordinary work on both sides of its one-shot
    // resumption.  `offset` belongs to the suspended clause, while
    // `adjusted` belongs to the resumed residual that must run after the
    // inner frame is uninstalled and before the outer frame is resumed.
    let source = "effect Ask { [1,1] ask() -> i64; } effect Ping { [1,1] ping(seed: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with outer => handle Ping::ping(40) { Ping::ping(_) with inner => { let offset = 1; let value = inner(40 + offset); let adjusted = value + 1; outer(adjusted) } } } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_nested_arm_residual_that_captures_inner_payload() {
    // Inner payload registers belong to the selected handler clause, not the
    // restored continuation after `inner(...)`.  This must fail before VM
    // emission rather than becoming a verifier ReadBeforeWrite.
    let source = "effect Ask { [1,1] ask() -> i64; } effect Ping { [1,1] ping(seed: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with outer => handle Ping::ping(40) { Ping::ping(seed) with inner => { let value = inner(1); outer(value + seed) } } } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("inner payload escaped into nested resumption residual")
    };
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "G6005"
                && diagnostic
                    .message
                    .contains("not retained across the inner resumption")
        }),
        "missing nested residual retention diagnostic: {diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "G7005"),
        "residual must not reach VM verification: {diagnostics:#?}"
    );
}

#[test]
fn service_preserves_generic_effect_identity_across_nested_arm_resumption() {
    let source = "effect Ask<T> { [1,1] ask(value: T) -> T; } effect Ping<T> { [1,1] ping(value: T) -> T; } pub fn main() -> i64 { handle Ask<i64>::ask(0) { Ask<i64>::ask(_) with outer => handle Ping<i64>::ping(41) { Ping<i64>::ping(_) with inner => { let value = inner(41); outer(value) } } } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_forwards_nested_generic_operation_instances_through_materialized_calls() {
    let source = "effect Exchange<T> { [1,1] exchange<U>(value: T, reply: U) -> U; } pub fn leaf<T, U>(value: T, reply: U) -> U / Exchange<T> { Exchange<T>::exchange<U>(value, reply) } pub fn partial<U>(value: i64, reply: U) -> U / Exchange<i64> { handle leaf(value, reply) { Exchange<i64>::exchange<U>(0, reply, k) => k(reply) } } pub fn main() -> Text { handle partial(7, \"payload\") { Exchange<i64>::exchange<Text>(_, reply, k) => k(reply) } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("a refutable generic inner handler must forward to the outer concrete instance");
    let artifact = outcome.artifact.expect("build must publish a VM artifact");
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Forward))
    }));
    assert_eq!(artifact.run_text().unwrap(), "payload");
}

#[test]
fn service_resumes_an_outer_handler_after_an_inner_effectful_function_value_call() {
    let source = "effect Ask { [1,1] ask() -> i64; } effect Ping { [1,1] ping() -> i64; } pub fn invoke() -> i64 / Ping { Ping::ping() } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with outer => { let operation = invoke; handle operation() { Ping::ping() with inner => { let value = inner(41); outer(value) } } } } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
        "the nested computation must retain the function-value call"
    );
    assert_eq!(artifact.run_i64().unwrap(), 41);
}

#[test]
fn service_rejects_an_underused_outer_finite_resumption_through_nested_suspension() {
    let source = "effect Ops { [2,2] outer() -> i64; [1,1] inner() -> i64; } pub fn main() -> i64 { handle { handle Ops::outer() { Ops::inner(k) => k(40) } } { Ops::outer(k) => k(20) } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("underused nested finite resumption was accepted")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5012"),
        "missing quantitative nested-resumption diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_generated_resumption_shadows_a_same_named_parameter() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn identity(value: i64) -> i64 { value } pub fn choose(k: (i64) -> i64) -> i64 { handle Ask::ask() { Ask::ask(k) => k(42) } } pub fn main() -> i64 { choose(identity) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_named_functions_as_first_class_callable_values() {
    let source = "pub fn add_two(value: i64) -> i64 { value + 2 } pub fn apply(function: (i64) -> i64) -> i64 { function(40) } pub fn main() -> i64 { apply(add_two) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_excessive_local_callable_use_before_mir() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn twice(function: (i64) -> i64) -> i64 { function(20) + function(21) } pub fn main() -> i64 { twice(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("twice-used exact callable unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing structured callable-use diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_multiplies_captured_callable_use_by_closure_invocations() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn through_closure(function: (i64) -> i64) -> i64 { let call = (value: i64) -> i64 { function(value) }; call(20) + call(21) } pub fn main() -> i64 { through_closure(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("repeated closure capture unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing captured callable-use diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_preserves_a_move_captured_callable_obligation_in_its_closure() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn through(function: (i64) -> i64) -> i64 { let call = (value: i64) -> i64 { move function(value) }; call(41) } pub fn main() -> i64 { through(add_one) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_repeated_move_captured_callable_transfer_through_a_local_call() {
    // The receiver is local in this companion case.  Package linking must
    // not decide whether two sequential outgoing boundaries activate the
    // closure environment: both local and imported callables receive the
    // same exact capability transfer.
    let source = "pub fn invoke(callback: () -> i64) -> i64 { callback() } pub fn next(value: i64) -> i64 { value + 1 } pub fn run(function: (i64) -> i64) -> i64 { let callback = () -> i64 { move function(41) }; invoke(callback) + invoke(callback) } pub fn main() -> i64 { run(next) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!(
            "a move-captured callback was unexpectedly transferred twice through a local callable"
        );
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing local move-capture transfer diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_joins_alternative_move_captured_callable_transfers_at_handler_arms() {
    // Each arm receives the same lexical closure, but only one arm runs for
    // any performance.  The use summary must branch-hull these transfers;
    // treating the closure as globally memoized misses sequential uses,
    // while treating these arms as a sequence would reject valid code.
    let source = "effect Pick { [1,1] pick(value: Bool) -> i64; } pub fn invoke(callback: () -> i64) -> i64 { callback() } pub fn next(value: i64) -> i64 { value + 1 } pub fn run(value: Bool, function: (i64) -> i64) -> i64 { let callback = () -> i64 { move function(41) }; handle Pick::pick(value) { Pick::pick(true) => invoke(callback), Pick::pick(false) => invoke(callback) } } pub fn main() -> i64 { run(true, next) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_multiplies_move_captured_callable_use_through_handler_replay() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn replay(function: (i64) -> i64) -> i64 { handle { let value = Ask::ask(); let call = (input: i64) -> i64 { move function(input) }; call(value) } { Ask::ask() with k => k(20) + k(21) } } pub fn main() -> i64 { replay(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("replayed move capture unexpectedly satisfied an exact callable obligation");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing replayed move-capture quantity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_move_captures_aggregate_roots_for_partial_closure_moves() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn through(pair: Pair) -> i64 { let call = () -> i64 { let taken = move pair.function; taken(41) }; call() } pub fn main() -> i64 { through(Pair { function: add_one, value: 0 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_joins_partial_aggregate_move_captures_across_handler_arms() {
    let source = "effect Pick { [1,1] pick(value: Bool) -> i64; } pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn choose(value: Bool, pair: Pair) -> i64 { handle Pick::pick(value) { Pick::pick(true) => { let call = () -> i64 { let taken = move pair.function; taken(41) }; call() }, Pick::pick(false) => { let call = () -> i64 { let taken = move pair.function; taken(42) }; call() } } } pub fn main() -> i64 { choose(true, Pair { function: add_one, value: 0 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_cancellation_keeps_move_captured_callable_obligations_live() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn cancel(function: (i64) -> i64) -> i64 { handle { let call = (value: i64) -> i64 { move function(value) }; Ask::ask() } { Ask::ask() with _ => 0 } } pub fn main() -> i64 { cancel(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("cancelling a move-captured exact callable unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing cancellation move-capture quantity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_an_unfulfilled_callable_lower_bound_on_normal_exit() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn ignores(function: (i64) -> i64) -> i64 { 42 } pub fn main() -> i64 { ignores(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("unused exact callable unexpectedly satisfied its lower bound");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing callable lower-bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_checks_callable_lower_bounds_after_branch_hulls() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn choose(value: i64, function: (i64) -> i64) -> i64 { handle value { 0 => function(41), _ => 0 } } pub fn main() -> i64 { choose(0, add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("branch-optional callable use unexpectedly satisfied an exact lower bound");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing branch-hull callable lower-bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_transfers_callable_obligations_through_effect_operation_payloads() {
    let source = "effect Store { [1,1] save(callback: (i64) -> i64); } pub fn relay(callback: (i64) -> i64) -> () / {Store} { Store::save(callback) } pub fn main() -> i64 { 0 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
}

#[test]
fn service_checks_handler_payload_callable_obligations_per_selected_arm() {
    let source = "effect Invoke { [1,1] invoke(callback: (i64) -> i64) -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn main() -> i64 { handle Invoke::invoke(add_one) { Invoke::invoke(callback) => callback(41) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_keeps_handler_payload_callable_obligations_arm_local_through_closures() {
    let source = "effect Select { [1,1] first(callback: (i64) -> i64) -> i64; [1,1] second(callback: (i64) -> i64) -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn main() -> i64 { handle Select::first(add_one) { Select::first(callback) => { let relay = (value: i64) -> i64 { callback(value) }; relay(41) }, Select::second(callback) => callback(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_dropping_an_exact_handler_payload_callable() {
    let source = "effect Invoke { [1,1] invoke(callback: (i64) -> i64) -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn main() -> i64 { handle Invoke::invoke(add_one) { Invoke::invoke(callback) => 0 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("discarded exact handler payload callable unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing handler-payload callable-use diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_transfers_callable_obligations_through_a_typed_argument_boundary() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn apply(function: (i64) -> i64) -> i64 { function(41) } pub fn relay(function: (i64) -> i64) -> i64 { apply(function) } pub fn main() -> i64 { relay(add_one) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_treats_a_trailing_contextual_block_as_the_next_direct_call_argument() {
    let source = "pub fn apply(value: i64, callback: () -> i64) -> i64 { callback() } pub fn main() -> i64 { apply(0) { 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_opens_a_direct_fn_bound_for_a_trailing_contextual_block() {
    let source = "pub fn apply<F>(value: i64, callback: F) -> i64 where F: Fn<(), Output = i64> { callback() } pub fn main() -> i64 { apply(0) { 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_propagates_a_direct_call_result_into_nested_fn_bound_blocks() {
    let source = "pub enum Result<T, E> { Ok(T), Err(E) } pub fn first<B, F>(body: F) -> Result<B, ()> where F: Fn<(), Output = B> { Result::Ok(body()) } pub fn fallback<A, F>(value: Result<A, ()>, body: F) -> A where F: Fn<(), Output = A> { handle value { Result::Ok(value) => value, Result::Err(_) => body() } } pub fn main() -> i64 { fallback(first() { 42 }) { 0 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_reborrows_a_refined_enum_payload_by_position() {
    let source = r#"
        pub enum Result<T, E> { Ok(T), Err(E) }
        pub type Option<T> = Result<T, ()>;
        pub fn result_as_ref<'a, A, E>(value: &'a Result<A, E>) -> Result<&'a A, &'a E> {
            handle *value is Result::Ok(_) {
                true => Result::Ok(&value.0),
                false => Result::Err(&value.0),
            }
        }
        pub fn result_as_mut<'a, A, E>(value: &'a mut Result<A, E>) -> Result<&'a mut A, &'a mut E> {
            handle *value is Result::Ok(_) {
                true => Result::Ok(&mut value.0),
                false => Result::Err(&mut value.0),
            }
        }
        pub fn option_as_ref<'a, A>(value: &'a Option<A>) -> Option<&'a A> {
            handle *value is Result::Ok(_) {
                true => Result::Ok(&value.0),
                false => Result::Err(()),
            }
        }
        pub fn option_as_mut<'a, A>(value: &'a mut Option<A>) -> Option<&'a mut A> {
            handle *value is Result::Ok(_) {
                true => Result::Ok(&mut value.0),
                false => Result::Err(()),
            }
        }
        pub fn main() -> i64 {
            let result_ok = Result<i64, i64>::Ok(10);
            let result_err = Result<i64, i64>::Err(20);
            let option_some = Result<i64, ()>::Ok(30);
            let option_none = Result<i64, ()>::Err(());
            handle result_as_ref(&result_ok) {
                Result::Ok(value) => *value,
                Result::Err(value) => *value,
            } + handle result_as_mut(&mut result_err) {
                Result::Ok(value) => *value,
                Result::Err(value) => *value,
            } + handle option_as_ref(&option_some) {
                Result::Ok(value) => *value,
                Result::Err(_) => 0,
            } + handle option_as_mut(&mut option_none) {
                Result::Ok(value) => *value,
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 60);
}

#[test]
fn service_lowers_non_tail_completion_operands_into_vm_cfg() {
    let source = r#"
        pub fn main() -> i64 {
            handle 40 {
                40 => 40,
                _ => 0,
            } + handle 2 {
                2 => 2,
                _ => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_non_tail_completion_let_initializers_into_vm_cfg() {
    let source = r#"
        pub fn main() -> i64 {
            let left = handle 20 {
                20 => 20,
                _ => 0,
            };
            let right = handle 22 {
                22 => 22,
                _ => 0,
            };
            left + right
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_leaves_a_label_from_a_plain_completion_arm() {
    let source = r#"
        pub fn main() -> i64 {
            label done {
                handle 40 {
                    40 => transfer done 42,
                    _ => 0,
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_plain_completion_label_matrix_preserves_fallback_and_call_results() {
    let source = r#"
        pub fn choose(value: i64) -> i64 {
            label done {
                handle value {
                    40 => transfer done 42,
                    _ => 0,
                }
            }
        }
        pub fn main() -> i64 { choose(40) + choose(1) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejoins_nested_plain_completion_label_transfers() {
    let source = r#"
        pub fn main() -> i64 {
            label outer {
                label inner {
                    handle 40 {
                        40 => transfer inner 40,
                        _ => 0,
                    }
                } + 2
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_leaves_a_label_from_an_ordered_binary_operand() {
    let source = r#"
        pub fn main() -> i64 {
            label done { 1 + transfer done 42 }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_leaves_a_label_from_a_later_call_argument() {
    let source = r#"
        pub fn ignored(left: i64, right: i64) -> i64 { left + right }
        pub fn main() -> i64 {
            label done { ignored(1, transfer done 42) }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_label_transfer_respects_lazy_boolean_branch_selection() {
    for (source, expected) in [
        (
            "pub fn main() -> Bool { label done { false and transfer done true } }",
            false,
        ),
        (
            "pub fn main() -> Bool { label done { true and transfer done true } }",
            true,
        ),
        (
            "pub fn main() -> Bool { label done { true or transfer done false } }",
            true,
        ),
        (
            "pub fn main() -> Bool { label done { false or transfer done true } }",
            true,
        ),
    ] {
        let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
        assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
        assert_eq!(outcome.artifact.unwrap().run_bool().unwrap(), expected);
    }
}

#[test]
fn service_lazy_label_transfer_rejoins_a_bound_continuation() {
    let source = r#"
        pub fn main() -> Bool {
            let result = label done { false or transfer done true };
            result
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert!(outcome.artifact.unwrap().run_bool().unwrap());
}

#[test]
fn service_nested_completion_label_transfer_bypasses_its_strict_suffix() {
    let source = r#"
        pub fn choose(value: i64) -> i64 {
            label done {
                1 + handle value {
                    40 => transfer done 42,
                    _ => 0,
                }
            }
        }
        pub fn main() -> i64 { choose(40) + choose(1) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    // The transfer arm skips the `+ 1` continuation (42); the fallback arm
    // reaches it normally (1).
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_nested_effect_handler_label_transfer_leaves_after_strict_prefix() {
    let source = r#"
        effect Ask { [1, 1] ask() -> i64; }
        pub fn main() -> i64 {
            label done {
                1 + handle Ask::ask() {
                    Ask::ask() => transfer done 42,
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_assignment_value_label_transfer_exits_before_the_store() {
    let source = r#"
        pub fn main() -> i64 {
            let value = 0;
            let slot = &mut value;
            label done {
                *slot = transfer done 42;
                0
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_refutable_handler_label_transfers_keep_source_order() {
    let source = r#"
        effect Ask { [1, 1] ask(value: i64) -> i64; }
        pub fn choose(value: i64) -> i64 {
            label done {
                1 + handle Ask::ask(value) {
                    Ask::ask(1) => transfer done 41,
                    Ask::ask(other) => transfer done other,
                }
            }
        }
        pub fn main() -> i64 { choose(1) + choose(2) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_label_transfer_exits_every_strict_aggregate_constructor() {
    let cases = [
        (
            "pub fn main() -> i64 { label done { (1, transfer done 42); 0 } }",
            "tuple",
        ),
        (
            "pub fn main() -> i64 { label done { [1, transfer done 42]; 0 } }",
            "array",
        ),
        (
            "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { label done { Pair { left: 1, right: transfer done 42 }; 0 } }",
            "record",
        ),
        (
            "pub enum Result { Pair(i64, i64) } pub fn main() -> i64 { label done { Result::Pair(1, transfer done 42); 0 } }",
            "enum",
        ),
    ];
    for (source, shape) in cases {
        let outcome = StageZeroCompiler::new()
            .compile(request(source))
            .unwrap_or_else(|error| panic!("{shape} label transfer failed to compile: {error:#?}"));
        assert!(
            outcome.diagnostics.is_empty(),
            "{shape} label transfer diagnostics: {:#?}",
            outcome.diagnostics
        );
        assert_eq!(
            outcome.artifact.unwrap().run_i64().unwrap(),
            42,
            "{shape} constructor must not evaluate its strict suffix after transfer"
        );
    }
}

#[test]
fn service_label_transfer_exits_from_an_effect_argument_before_performance() {
    let source = r#"
        effect Ask { [1, 1] ask(value: i64) -> i64; }
        pub fn main() -> i64 {
            label done {
                handle Ask::ask(transfer done 42) {
                    Ask::ask(value) => value,
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_refutable_handler_mixes_normal_and_label_transfer_outcomes() {
    let source = r#"
        effect Ask { [1, 1] ask(value: i64) -> i64; }
        pub fn choose(value: i64) -> i64 {
            label done {
                handle Ask::ask(value) {
                    Ask::ask(0) => 1,
                    Ask::ask(other) => transfer done other,
                }
            }
        }
        pub fn main() -> i64 { choose(0) + choose(41) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_result_may_transfer_to_an_enclosing_label() {
    let source = r#"
        effect Ask { [1, 1] ask() -> i64; }
        pub fn worker() -> i64 / Ask {
            let value = Ask::ask();
            value + 1
        }
        pub fn main() -> i64 {
            label done {
                handle worker() {
                    Ask::ask() with k => transfer done k(41),
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_allows_an_immediately_invoked_closure_to_capture_a_resumption() {
    let source = r#"
        effect Ask { [1, 1] ask() -> i64; }
        pub fn main() -> i64 {
            handle Ask::ask() {
                Ask::ask() with k => {
                    let resume = (value: i64) -> i64 { k(value) };
                    resume(42)
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_allows_an_immediately_invoked_closure_to_capture_a_refinement_binder() {
    let source = r#"
        pub enum Result { Ok(i64), Err }
        pub fn main() -> i64 {
            let result = Result::Ok(42);
            handle result is Result::Ok(value) {
                true => {
                    let read = () -> i64 { value };
                    read()
                },
                false => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_trait_methods_with_independent_impl_head_generics() {
    let source = r#"
        trait Select<T> { fn select(receiver: Self, value: T) -> T; }
        struct Box<T> { payload: T }
        impl<T, U> Select<T> for Box<U> {
            fn select(receiver: Self, value: T) -> T { value }
        }
        pub fn main() -> i64 {
            Select<i64>::select(Box { payload: "tag" }, 42)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_multi_operation_handler_may_cancel_to_an_enclosing_label_after_a_resume() {
    let source = r#"
        effect Console {
            [1, 1] read(value: i64) -> i64;
            [0, 1] write(value: i64) -> i64;
        }
        pub fn worker() -> i64 / Console {
            let value = Console::read(40);
            Console::write(value)
        }
        pub fn main() -> i64 {
            label done {
                handle worker() {
                    Console::read(value) with k => k(value + 2),
                    Console::write(value, _) => transfer done value,
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_partial_handler_forwarding_may_reach_an_outer_label_transfer() {
    let source = r#"
        effect Ask { [0, 1] ask(value: i64) -> i64; }
        pub fn worker() -> i64 / Ask { Ask::ask(42) }
        pub fn main() -> i64 {
            label done {
                handle {
                    handle worker() {
                        Ask::ask(0, _) => 0,
                    }
                } {
                    Ask::ask(value, _) => transfer done value,
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_replayed_resumption_result_may_transfer_to_an_enclosing_label() {
    let source = r#"
        effect Ask { [2, 2] ask() -> i64; }
        pub fn worker() -> i64 / Ask {
            let value = Ask::ask();
            value + 1
        }
        pub fn main() -> i64 {
            label done {
                handle worker() {
                    Ask::ask(k) => {
                        let total = k(20) + k(21);
                        transfer done total
                    },
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_completion_after_a_resumption_may_transfer_to_an_enclosing_label() {
    let source = r#"
        effect Ask { [1, 1] ask() -> i64; }
        pub fn main() -> i64 {
            label done {
                handle Ask::ask() {
                    value => transfer done value + 1,
                    Ask::ask(k) => k(41),
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_composes_generic_effects_closures_and_finite_replay_across_a_call() {
    let source = r#"
        effect Echo<T> { [2, 2] echo(value: T) -> T; }
        pub fn relay<T>(value: T, transform: (T) -> T) -> T / Echo<T> {
            transform(Echo<T>::echo(value))
        }
        pub fn main() -> i64 {
            let increment = (value: i64) -> i64 { value + 1 };
            handle relay(20, increment) {
                Echo<i64>::echo(value, k) => k(value) + k(value),
            }
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("generic effect replay through a captured callable must compile");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn manifest_bound_generic_int_bit_and_specializes_u8() {
    let mut input = request(
        "fn __g1_int_bit_and<T>(left: T, right: T) -> T { () } \
         pub fn main() -> u8 { __g1_int_bit_and<u8>(42, 15) }",
    );
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::IntBitAnd,
        "__g1_int_bit_and",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("generic integer primitives must materialize for every concrete integer width")
        .artifact
        .expect("a successful build must publish an artifact");
    assert_eq!(artifact.run_u8().unwrap(), 10);
}

#[test]
fn generic_integer_shift_wrappers_materialize_signed_unsigned_and_trapping_widths() {
    // `shift` itself remains polymorphic, so its MIR initially contains an
    // `IntGenericIntrinsic`.  Each entry point below forces a distinct
    // specialization and proves the VM retains the documented integer-width
    // semantics rather than falling back to the legacy i64-only instructions.
    let compile = |source: &str| {
        let mut input = request(source);
        input.runtime_manifest = Some(RuntimeManifestInput {
            standard_library: PackageKey("app@0.1.0".into()),
            host_imports: vec![],
            selectors: [
                (PrimitiveRole::IntShr, "__g1_int_shr"),
                (PrimitiveRole::IntWrappingNeg, "__g1_int_wrapping_neg"),
            ]
            .into_iter()
            .map(|(role, name)| PrimitiveSelector {
                role,
                module_path: "crate".into(),
                name: name.into(),
            })
            .collect(),
        });
        StageZeroCompiler::new()
            .compile(input)
            .expect("generic integer shift wrapper must materialize")
            .artifact
            .expect("successful build must publish a VM artifact")
    };

    let signed = compile(
        "fn __g1_int_shr<T>(value: T, count: u32) -> T { () } fn __g1_int_wrapping_neg<T>(value: T) -> T { () } \
         pub fn shift<T>(value: T, count: u32) -> T { __g1_int_shr<T>(move value, move count) } \
         pub fn negate<T>(value: T) -> T { __g1_int_wrapping_neg<T>(move value) } \
         pub fn value() -> i8 { 1 } pub fn count() -> u32 { 1 } \
         pub fn main() -> i8 { shift(negate(value()), count()) }",
    );
    assert_eq!(signed.run_i8().unwrap(), -1);

    let unsigned = compile(
        "fn __g1_int_shr<T>(value: T, count: u32) -> T { () } fn __g1_int_wrapping_neg<T>(value: T) -> T { () } \
         pub fn shift<T>(value: T, count: u32) -> T { __g1_int_shr<T>(move value, move count) } \
         pub fn value() -> u8 { 128 } pub fn count() -> u32 { 1 } \
         pub fn main() -> u8 { shift(value(), count()) }",
    );
    assert_eq!(unsigned.run_u8().unwrap(), 64);

    let out_of_range = compile(
        "fn __g1_int_shr<T>(value: T, count: u32) -> T { () } fn __g1_int_wrapping_neg<T>(value: T) -> T { () } \
         pub fn shift<T>(value: T, count: u32) -> T { __g1_int_shr<T>(move value, move count) } \
         pub fn value() -> u8 { 1 } pub fn count() -> u32 { 8 } \
         pub fn main() -> u8 { shift(value(), count()) }",
    );
    let error = out_of_range.run_u8();
    assert!(matches!(error, Err(VmArtifactError::ArithmeticOverflow)), "{error:?}");
}

#[test]
fn service_reborrows_each_nested_multi_variant_refinement_payload() {
    let source = r#"
        fn __g1_abort() -> ! { () }
        pub enum Tri { First(i64), Second(i64), Third(i64) }
        pub fn view<'a>(value: &'a Tri) -> &'a i64 {
            handle *value is Tri::First(_) {
                true => &value.0,
                false => handle *value is Tri::Second(_) {
                    true => &value.0,
                    false => handle *value is Tri::Third(_) {
                        true => &value.0,
                        false => __g1_abort(),
                    },
                },
            }
        }
        pub fn main() -> i64 {
            let first = Tri::First(10);
            let second = Tri::Second(20);
            let third = Tri::Third(12);
            *view(&first) + *view(&second) + *view(&third)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_refuses_an_ambiguous_multi_variant_negative_payload_projection() {
    let source = r#"
        pub enum Tri { First(i64), Second(i64), Third(i64) }
        pub fn invalid<'a>(value: &'a Tri) -> &'a i64 {
            handle *value is Tri::First(_) {
                true => &value.0,
                false => &value.0,
            }
        }
        pub fn main() -> i64 { 0 }
    "#;
    let error = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4128"),
        "missing ambiguous multi-variant refinement diagnostic: {error:#?}"
    );
}

#[test]
fn service_lowers_a_top_level_value_alias_to_its_callable_target() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } let increment = add_one; pub fn main() -> i64 { increment(41) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_a_qualified_value_alias_receiver_spelling() {
    let source = "pub fn __g1_vec_len(value: i64) -> i64 { value + 1 } let Vec::len = __g1_vec_len; pub fn main() -> i64 { Vec::len(41) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_freezes_canonical_enum_constructor_value_aliases() {
    let source = "pub enum Result { Ok(i64), Err } let Option::Some = Result::Ok; pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_public_value_aliases_across_modules() {
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(
            "pub mod api; pub fn main() -> i64 { api::increment(41) }",
            &[(
                "api",
                "pub fn add_one(value: i64) -> i64 { value + 1 } pub let increment = add_one;",
            )],
        ))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_cyclic_or_unknown_top_level_value_aliases() {
    for source in [
        "let first = second; let second = first; pub fn main() -> i64 { 0 }",
        "let missing = not_found; pub fn main() -> i64 { 0 }",
    ] {
        let error = StageZeroCompiler::new()
            .compile(request(source))
            .unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == "G3340"),
            "missing value-alias interface diagnostic: {error:#?}"
        );
    }
}

#[test]
fn service_rejects_sequential_callable_escapes_that_exceed_one_owner_contract() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn apply(function: (i64) -> i64, value: i64) -> i64 { function(value) } pub fn relay(function: (i64) -> i64) -> i64 { apply(function, 20) + apply(function, 21) } pub fn main() -> i64 { relay(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("two sequential exact callable transfers unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "missing accumulated callable-escape diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_allows_one_typed_callable_escape_from_each_completion_branch() {
    let source = "pub enum Choice { Left, Right } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn apply(function: (i64) -> i64, value: i64) -> i64 { function(value) } pub fn relay(function: (i64) -> i64, choice: Choice) -> i64 { handle choice { Choice::Left => apply(function, 20), Choice::Right => apply(function, 21) } } pub fn main() -> i64 { relay(add_one, Choice::Left) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 21);
}

#[test]
fn service_rejects_double_use_of_a_callable_extracted_by_a_record_completion_pattern() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn relay(pair: Pair) -> i64 { handle pair { Pair { function, value: _ } => function(20) + pair.function(21) } } pub fn main() -> i64 { relay(Pair { function: add_one, value: 0 }) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("pattern extraction duplicated an affine callable owner");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011" || diagnostic.code == "G5013"),
        "missing pattern-extraction callable ownership diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_lowers_enum_callable_payload_extraction_through_completion_dispatch() {
    let source = "pub enum Choice { Some((i64) -> i64), None } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn relay(choice: Choice) -> i64 { handle choice { Choice::Some(function) => function(41), Choice::None => 0 } } pub fn main() -> i64 { relay(Choice::Some(add_one)) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_a_struct_containing_a_callable_to_a_matching_parameter_contract() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn consume(pair: Pair) -> i64 { pair.function(41) } pub fn relay(pair: Pair) -> i64 { consume(pair) } pub fn main() -> i64 { relay(Pair { function: add_one, value: 0 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_a_generic_struct_callable_field_with_its_instantiated_contract() {
    let source = "pub type Callback = (i64) -> i64; pub struct Pair<T> { function: T, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn consume(pair: Pair<Callback>) -> i64 { pair.function(41) } pub fn relay(pair: Pair<Callback>) -> i64 { consume(pair) } pub fn main() -> i64 { relay(Pair<Callback> { function: add_one, value: 0 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_struct_callable_contracts_through_effect_payload_patterns() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } effect Dispatch { [1, 1] take(pair: Pair) -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn relay(pair: Pair) -> i64 / Dispatch { Dispatch::take(pair) } pub fn main() -> i64 { handle relay(Pair { function: add_one, value: 0 }) { Dispatch::take(Pair { function: callback, value: _ }) => callback(41) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_a_maybe_skipped_exact_callable_escape_at_a_completion_join() {
    let source = "pub enum Choice { Left, Right } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn apply(function: (i64) -> i64, value: i64) -> i64 { function(value) } pub fn relay(function: (i64) -> i64, choice: Choice) -> i64 { handle choice { Choice::Left => apply(function, 20), Choice::Right => 0 } } pub fn main() -> i64 { relay(add_one, Choice::Left) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("a conditionally skipped exact callable transfer unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "missing conditional callable-transfer diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_direct_callable_use_followed_by_a_typed_escape() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn apply(function: (i64) -> i64, value: i64) -> i64 { function(value) } pub fn relay(function: (i64) -> i64) -> i64 { function(20) + apply(function, 21) } pub fn main() -> i64 { relay(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("a direct use followed by an exact callable transfer unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "missing combined direct-use and escape diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_transfers_an_exact_callable_obligation_out_of_a_tuple_field_move() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn take(function: (i64) -> i64) -> i64 { let pair = Pair { function: function, value: 0 }; let taken = move pair.function; taken(41) } pub fn main() -> i64 { take(add_one) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_overwriting_an_unfulfilled_aggregate_callable_obligation() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn replace(function: (i64) -> i64) -> i64 { let pair = Pair { function: function, value: 0 }; pair.function = (value: i64) -> i64 { value }; 0 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn main() -> i64 { replace(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("overwriting an exact aggregate callback unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5014"),
        "missing aggregate overwrite obligation diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_counts_callable_obligations_captured_through_an_aggregate_closure() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn through(function: (i64) -> i64) -> i64 { let pair = Pair { function: function, value: 0 }; let call = (value: i64) -> i64 { pair.function(value) }; call(41) } pub fn main() -> i64 { through(add_one) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_checks_aggregate_callable_obligations_at_handler_branch_exits() {
    let source = "effect Pick { [0,1] pick(value: Bool) -> i64; } pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn choose(value: Bool, function: (i64) -> i64) -> i64 { let pair = Pair { function: function, value: 0 }; handle Pick::pick(value) { Pick::pick(true) => pair.function(41), Pick::pick(false) => 0 } } pub fn main() -> i64 { choose(true, add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("handler-optional aggregate callback use unexpectedly satisfied exact lower bound");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing aggregate handler-join obligation diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_tracks_callable_obligations_projected_from_aggregate_parameters() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn apply(pair: Pair) -> i64 { pair.function(41) } pub fn main() -> i64 { apply(Pair { function: add_one, value: 0 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_discarding_a_projected_aggregate_parameter_callable() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn discard(pair: Pair) -> i64 { let ignored = move pair.function; 0 } pub fn main() -> i64 { discard(Pair { function: add_one, value: 0 }) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("discarded aggregate parameter callback unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing projected partial-move lower-bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_dropping_an_unprojected_nominal_callable_parameter() {
    let source = "pub struct CallbackBox { callback: (i64) -> i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn discard(box: CallbackBox) -> i64 { 0 } pub fn main() -> i64 { discard(CallbackBox { callback: add_one }) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("discarding a whole exact-callback struct parameter unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing whole-nominal callable lower-bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_tracks_generic_nominal_callable_fields_through_closure_execution() {
    let source = "pub struct CallbackBox<T> { callback: T } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn invoke(box: CallbackBox<(i64) -> i64>) -> i64 { let call = (value: i64) -> i64 { box.callback(value) }; call(41) } pub fn main() -> i64 { invoke(CallbackBox { callback: add_one }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_checks_nominal_callable_payloads_at_handler_arm_boundaries() {
    let source = "pub struct CallbackBox { callback: (i64) -> i64 } effect Invoke { invoke(box: CallbackBox) -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn main() -> i64 { handle Invoke::invoke(CallbackBox { callback: add_one }) { Invoke::invoke(box) => 0 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("handler arm dropped an exact callback nested in its payload struct");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing handler nominal-payload lower-bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_executes_nominal_callable_payloads_captured_by_handler_closures() {
    let source = "pub struct CallbackBox { callback: (i64) -> i64 } effect Invoke { invoke(box: CallbackBox) -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn main() -> i64 { handle Invoke::invoke(CallbackBox { callback: add_one }) { Invoke::invoke(box) => { let relay = (value: i64) -> i64 { box.callback(value) }; relay(41) } } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_overwriting_a_projected_aggregate_parameter_callable() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn replace(pair: Pair) -> i64 { pair.function = (value: i64) -> i64 { value }; 0 } pub fn main() -> i64 { replace(Pair { function: add_one, value: 0 }) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("overwritten aggregate parameter callback unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5014"),
        "missing projected callable overwrite diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_transfers_projected_parameter_callable_through_partial_move_and_closure() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn through(pair: Pair) -> i64 { let taken = move pair.function; let call = (value: i64) -> i64 { taken(value) }; call(41) } pub fn main() -> i64 { through(Pair { function: add_one, value: 0 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_checks_projected_parameter_callable_at_handler_branch_join() {
    let source = "effect Pick { [0,1] pick(value: Bool) -> i64; } pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn choose(value: Bool, pair: Pair) -> i64 { handle Pick::pick(value) { Pick::pick(true) => pair.function(41), Pick::pick(false) => 0 } } pub fn main() -> i64 { choose(true, Pair { function: add_one, value: 0 }) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("handler branch unexpectedly satisfied projected callback obligation");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing projected callable branch-hull diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_callable_only_reachable_after_a_discarded_handler_operation() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn discard(function: (i64) -> i64) -> i64 { handle { let value = Ask::ask(); function(41) } { Ask::ask() with _ => 0 } } pub fn main() -> i64 { discard(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("callback after discarded operation unexpectedly satisfied its use obligation");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing discarded-handler callable-use diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_counts_callable_prefix_before_a_discarded_handler_operation() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn consume(function: (i64) -> i64) -> i64 { handle { function(41); Ask::ask() } { Ask::ask() with _ => 0 } } pub fn main() -> i64 { consume(add_one) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 0);
}

#[test]
fn service_rejects_callable_replayed_by_a_direct_handler_continuation() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn replay(function: (i64) -> i64) -> i64 { handle { let value = Ask::ask(); function(value) } { Ask::ask() with k => k(20) + k(21) } } pub fn main() -> i64 { replay(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("replayed callback unexpectedly satisfied its exact use obligation");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing continuation-replay callable-use diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_multiplies_closure_captures_by_direct_handler_replay() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn replay(function: (i64) -> i64) -> i64 { handle { let value = Ask::ask(); let call = (input: i64) -> i64 { function(input) }; call(value) } { Ask::ask() with k => k(20) + k(21) } } pub fn main() -> i64 { replay(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("replayed closure capture unexpectedly satisfied exact use");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing replayed closure-capture diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_executes_a_once_replayed_direct_handler_residual() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn replay(function: (i64) -> i64) -> i64 { handle { let value = Ask::ask(); function(value) } { Ask::ask() with k => k(41) } } pub fn main() -> i64 { replay(add_one) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_a_concretely_instantiated_generic_function_value() {
    let source = "pub fn identity<T>(value: T) -> T { value } pub fn apply(function: (i64) -> i64) -> i64 { function(42) } pub fn main() -> i64 { apply(identity) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
    assert!(
        outcome
            .instance_graph
            .expect("closed function value must discover an executable instance")
            .ordered()
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
}

#[test]
fn service_rejects_direct_resumption_overuse_against_an_exact_quantity() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => k(1) + k(2) + k(3) } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("overused direct resumption unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6005"),
        "missing direct-resumption quantity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_allows_an_explicit_unused_affine_direct_resumption() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_allows_a_once_callback_transfer_through_a_once_resumed_handler_suffix() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn apply(callback: (i64) -> i64, value: i64) -> i64 { callback(value) } pub fn worker(callback: (i64) -> i64) -> i64 { handle { let value = Ask::ask(); apply(callback, value) } { Ask::ask(k) => k(41) } } pub fn main() -> i64 { 0 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
}

#[test]
fn service_rejects_replaying_a_once_callback_transfer_through_a_handler_suffix() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn apply(callback: (i64) -> i64, value: i64) -> i64 { callback(value) } pub fn worker(callback: (i64) -> i64) -> i64 { handle { let value = Ask::ask(); apply(callback, value) } { Ask::ask(k) => k(40) + k(41) } } pub fn main() -> i64 { 0 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("replayed once-only callback transfer unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "missing replayed callback-transfer quantity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_intercepts_a_direct_effectful_helper_call_with_the_enclosing_handler() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn helper(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn main() -> i64 { handle helper(41) { Ask::ask(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_helper_parameter_order_when_intercepting_a_performance() {
    let source = "effect Ask { [1,1] ask(left: i64, right: i64) -> i64; } pub fn helper(left: i64, right: i64) -> i64 / Ask { Ask::ask(left, right) } pub fn main() -> i64 { handle helper(20, 22) { Ask::ask(left, right) => left + right } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_intercepts_a_helper_performance_through_local_aliases_and_reordering() {
    let source = "effect Ask { [1,1] ask(left: i64, right: i64) -> i64; } pub fn helper(left: i64, right: i64) -> i64 / Ask { let first = right; let second = left; Ask::ask(first, second) } pub fn main() -> i64 { handle helper(20, 22) { Ask::ask(left, right) => left * 10 + right } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 240);
}

#[test]
fn service_instantiates_generic_helper_effect_rows_before_static_handler_interception() {
    let source = "effect Ask<T> { [1,1] ask(value: T) -> T; } pub fn helper<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) } pub fn main() -> i64 { handle helper(41) { Ask<i64>::ask(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_handles_an_indirect_generic_helper_performance_through_a_vm_frame() {
    let source = "effect Ask<T> { [1,1] ask(value: T) -> T; } pub fn helper<T>(value: T) -> T / Ask<T> { let copy = value; Ask<T>::ask(copy) } pub fn main() -> i64 { handle helper(41) { Ask<i64>::ask(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. })),
        "indirect helper interception must retain a VM handler frame"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Call { .. })),
        "generic helper invocation must remain an ordinary VM call"
    );
    assert!(
        program
            .functions
            .iter()
            .filter(|(definition, _)| **definition != program.entry)
            .any(
                |(_, function)| function.instructions.iter().any(|instruction| matches!(
                    instruction,
                    VmInstruction::Perform { effect_arguments, .. }
                        if effect_arguments.as_slice() == [VmGenericArgument::Type(VmType::I64)]
                ))
            ),
        "the materialized helper performance must use Ask<i64>, never Ask<T>"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_generic_handler_frame_effect_identities() {
    let source = "effect Ask<T> { [1,1] ask(value: T) -> T; } pub fn leaf<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) } pub fn helper<T>(value: T) -> T / Ask<T> { handle leaf<T>(value) { Ask<T>::ask(value) with k => k(value) } } pub fn main() -> i64 { handle helper(42) { Ask<i64>::ask(value) with k => k(value) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let concrete_i64 = [VmGenericArgument::Type(VmType::I64)];
    assert!(
        program
            .functions
            .values()
            .any(
                |function| function.instructions.iter().any(|instruction| matches!(
                    instruction,
                    VmInstruction::InstallHandler { effect_arguments, .. }
                        if effect_arguments.as_slice() == concrete_i64
                ))
            ),
        "materialized generic handler frames must use their concrete effect identity"
    );
    assert!(
        program
            .functions
            .values()
            .any(
                |function| function.instructions.iter().any(|instruction| matches!(
                    instruction,
                    VmInstruction::Perform { effect_arguments, .. }
                        if effect_arguments.as_slice() == concrete_i64
                ))
            ),
        "materialized generic performances must use the same concrete effect identity"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_a_mismatched_generic_effect_instance_at_a_callee_boundary() {
    let source = "effect State<T> { [1,1] get() -> i64; } pub fn helper<T>() -> i64 / State<T> { State<T>::get() } pub fn main() -> i64 { handle helper<Text>() { State<i64>::get() with k => k(42) } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("a State<i64> handler unexpectedly accepted a State<Text> callee")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "mismatched generic effect instance must remain in the outward row: {diagnostics:#?}"
    );
}

#[test]
fn service_handles_a_nontransparent_nested_callee_through_normal_vm_calls() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn leaf(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn helper(value: i64) -> i64 / Ask { let shifted = value + 1; leaf(shifted) } pub fn main() -> i64 { handle helper(40) { Ask::ask(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Call { .. })),
        "the outer handler must preserve the helper call boundary"
    );
    assert!(
        program
            .functions
            .iter()
            .filter(|(definition, _)| **definition != program.entry)
            .any(|(_, function)| function
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::Call { .. }))),
        "the nontransparent helper must retain its nested ordinary call"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_handles_an_effectful_function_value_through_a_dynamic_frame() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn helper(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn main() -> i64 { let operation = helper; handle operation(40) { Ask::ask(value) with k => k(value + 2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
        "effectful function value must retain an indirect VM call"
    );
    let Some(VmInstruction::MakeCallable { dst, .. }) = entry
        .instructions
        .iter()
        .find(|instruction| matches!(instruction, VmInstruction::MakeCallable { .. }))
    else {
        panic!("effectful function value must materialize a callable")
    };
    let VmType::Callable { effects, .. } = &entry.registers[*dst as usize] else {
        panic!("callable construction destination must retain callable ABI")
    };
    assert_eq!(effects.effects.len(), 1);
    assert!(effects.projections.is_empty());
    assert!(effects.tail.is_none());
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_propagates_a_closed_multi_operation_effect_summary_through_a_callee() {
    let source = "effect Console { [1,1] read() -> i64; [1,1] write(value: i64) -> i64; } pub fn helper() -> i64 / Console { let value = Console::read(); Console::write(value) } pub fn main() -> i64 { handle helper() { Console::read() with k => k(20), Console::write(value) with k => k(value + 2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. }))
            .count(),
        2,
        "one dynamic frame is required for each summarized operation"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Call { .. }))
    );
    assert_eq!(artifact.run_i64().unwrap(), 22);
}

#[test]
fn service_materializes_generic_multi_operation_effect_frames_across_a_callee() {
    let source = "effect State<T> { [1,1] read(value: T) -> T; [1,1] write(value: T) -> T; } pub fn helper<T>(value: T) -> T / State<T> { let read = State<T>::read(value); State<T>::write(read) } pub fn main() -> i64 { handle helper(40) { State<i64>::read(value) with k => k(value + 1), State<i64>::write(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(
                instruction,
                VmInstruction::InstallHandler { effect_arguments, .. }
                    if effect_arguments.as_slice() == [VmGenericArgument::Type(VmType::I64)]
            ))
            .count(),
        2,
        "one concrete State<i64> frame is required per summarized operation"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Call { .. })),
        "generic multi-operation helper must remain a normal VM call"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_uses_each_operation_continuation_type_across_a_multi_operation_call() {
    let source = "effect State { [1,1] read() -> Text; [1,1] write(value: i64) -> i64; } pub fn helper() -> i64 / State { let value = State::read(); let written = State::write(40); written + 2 } pub fn main() -> i64 { handle helper() { State::read() with k => k(\"ignored\"), State::write(value) with k => k(value) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry.instructions.iter().any(|instruction| matches!(
            instruction,
            VmInstruction::InstallHandler {
                operation: 0,
                resume_type: VmType::Text,
                ..
            }
        )),
        "read frame must inject the Text operation result, not helper's i64 result"
    );
    assert!(
        entry.instructions.iter().any(|instruction| matches!(
            instruction,
            VmInstruction::InstallHandler {
                operation: 1,
                resume_type: VmType::I64,
                ..
            }
        )),
        "write frame must retain its independent i64 operation result"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_dispatches_generic_multi_operation_effects_through_a_function_value() {
    let source = "effect State<T> { [1,1] read(value: T) -> T; [1,1] write(value: T) -> T; } pub fn helper<T>(value: T) -> T / State<T> { let read = State<T>::read(value); State<T>::write(read) } pub fn main() -> i64 { let operation = helper; handle operation(40) { State<i64>::read(value) with k => k(value + 1), State<i64>::write(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
        "generic multi-operation function values must keep their dynamic call boundary"
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(
                instruction,
                VmInstruction::InstallHandler { effect_arguments, .. }
                    if effect_arguments.as_slice() == [VmGenericArgument::Type(VmType::I64)]
            ))
            .count(),
        2
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_orders_refutable_handler_clauses_around_an_interprocedural_call() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn leaf(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn helper(value: i64) -> i64 / Ask { leaf(value) } pub fn main() -> i64 { handle helper(40) { Ask::ask(0) with k => k(1), Ask::ask(value) with k => k(value + 2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Call { .. })),
        "the protected helper must remain an ordinary VM call"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. })),
        "the ordered source matrix must install a dynamic handler frame"
    );
    assert!(
        program.functions.values().any(|function| {
            function
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::PatternTest { .. }))
                && function.instructions.iter().any(|instruction| {
                    matches!(
                        instruction,
                        VmInstruction::BranchBool {
                            then_target,
                            else_target,
                            ..
                        } if (*then_target as usize) < function.instructions.len()
                            && (*else_target as usize) < function.instructions.len()
                    )
                })
        }),
        "the leading refutable source clause must retain bounded true/false CFG edges"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_orders_generic_multi_operation_matrices_around_an_interprocedural_call() {
    let source = "effect Console<T> { [1, 1] read(value: T) -> Text; [1, 1] write(value: T) -> i64; } pub fn helper<T>(value: T) -> i64 / Console<T> { let read = Console<T>::read(value); Console<T>::write(value) } pub fn main() -> i64 { handle helper(40) { Console<i64>::read(0) with k => k(\"zero\"); Console<i64>::read(_) with k => k(\"value\"); Console<i64>::write(0) with k => k(0); Console<i64>::write(_) with k => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. }))
            .count(),
        2,
        "one dynamic frame is required for each independently ordered operation matrix"
    );
    assert!(entry.instructions.iter().any(|instruction| matches!(
        instruction,
        VmInstruction::InstallHandler {
            operation: 0,
            effect_arguments,
            resume_type: VmType::Text,
            ..
        } if effect_arguments.as_slice() == [VmGenericArgument::Type(VmType::I64)]
    )));
    assert!(entry.instructions.iter().any(|instruction| matches!(
        instruction,
        VmInstruction::InstallHandler {
            operation: 1,
            effect_arguments,
            resume_type: VmType::I64,
            ..
        } if effect_arguments.as_slice() == [VmGenericArgument::Type(VmType::I64)]
    )));
    assert!(
        program.functions.values().any(|function| function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::PatternTest { .. }))),
        "refutable source rows must remain VM pattern tests"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_orders_generic_multi_operation_matrices_through_a_function_value() {
    let source = "effect Console<T> { [1, 1] read(value: T) -> Text; [1, 1] write(value: T) -> i64; } pub fn helper<T>(value: T) -> i64 / Console<T> { let read = Console<T>::read(value); Console<T>::write(value) } pub fn main() -> i64 { let operation = helper; handle operation(40) { Console<i64>::read(0) with k => k(\"zero\"); Console<i64>::read(_) with k => k(\"value\"); Console<i64>::write(0) with k => k(0); Console<i64>::write(_) with k => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
        "the matrix must keep the function-value call boundary"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_a_forged_ordered_matrix_handler_target() {
    let source = "effect Console<T> { [1, 1] read(value: T) -> Text; [1, 1] write(value: T) -> i64; } pub fn helper<T>(value: T) -> i64 / Console<T> { let read = Console<T>::read(value); Console<T>::write(value) } pub fn main() -> i64 { handle helper(40) { Console<i64>::read(0) with k => k(\"zero\"); Console<i64>::read(_) with k => k(\"value\"); Console<i64>::write(0) with k => k(0); Console<i64>::write(_) with k => k(42) } }";
    let artifact = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap();
    let mut forged = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = forged.functions.get_mut(&forged.entry).unwrap();
    let VmInstruction::InstallHandler { target, .. } = entry
        .instructions
        .iter_mut()
        .find(|instruction| {
            matches!(
                instruction,
                VmInstruction::InstallHandler { operation: 0, .. }
            )
        })
        .expect("generated ordered matrix installs its read frame")
    else {
        unreachable!("the selected instruction is an InstallHandler")
    };
    *target = 0;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(
        decode_and_verify_program(&encode_program(&forged)).is_err(),
        "a forged caller cannot make normal entry flow reach a handler clause"
    );
}

#[test]
fn service_forwards_a_partial_refutable_interprocedural_handler_to_an_outer_frame() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn leaf(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn partial(value: i64) -> i64 / Ask { handle leaf(value) { Ask::ask(0) with k => k(1) } } pub fn main() -> i64 { handle partial(40) { Ask::ask(value) with k => k(value + 2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(
        program.functions.values().any(|function| {
            function
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. }))
                && function
                    .instructions
                    .iter()
                    .any(|instruction| matches!(instruction, VmInstruction::Call { .. }))
                && function
                    .instructions
                    .iter()
                    .any(|instruction| matches!(instruction, VmInstruction::PatternTest { .. }))
                && function
                    .instructions
                    .iter()
                    .any(|instruction| matches!(instruction, VmInstruction::Forward))
        }),
        "the partial callee matrix must preserve its call, frame, test, and forwarding edge together"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_a_partial_multi_operation_matrix_to_an_outer_handler() {
    let source = "effect Console<T> { [1, 1] read(value: T) -> T; [1, 1] write(value: T) -> T; } pub fn helper<T>(value: T) -> T / Console<T> { Console<T>::read(value) } pub fn partial(value: i64) -> i64 / Console<i64> { handle helper(value) { Console<i64>::read(0) with k => k(1); Console<i64>::write(_) with k => k(0) } } pub fn main() -> i64 { handle partial(40) { Console<i64>::read(value) with k => k(value + 2); Console<i64>::write(value) with k => k(value) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(
        program.functions.values().any(|function| {
            function
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::PatternTest { .. }))
                && function
                    .instructions
                    .iter()
                    .any(|instruction| matches!(instruction, VmInstruction::Forward))
        }),
        "a failed partial row must forward its original suspended operation"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_replays_a_cross_call_continuation_with_resume_return() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn leaf() -> i64 / Ask { Ask::ask() } pub fn helper() -> i64 / Ask { leaf() } pub fn main() -> i64 { handle { let value = helper(); let mutable = value; mutable = mutable + 1; mutable } { Ask::ask(k) => k(20) + k(21) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Call { .. })),
        "the replayed protected computation must retain its helper call"
    );
    assert!(
        entry.instructions.iter().any(|instruction| matches!(
            instruction,
            VmInstruction::InstallHandler {
                continuation: VmContinuationPolicy::Replay { uses: 2 },
                ..
            }
        )),
        "the cross-call continuation must be retained by a replayable VM frame"
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::ResumeReturn { .. }))
            .count(),
        2,
        "each statically required replay must return to the handler clause"
    );
    assert_eq!(artifact.run_i64().unwrap(), 43);
}

#[test]
fn service_preserves_a_three_shot_replay_budget_through_the_vm() {
    let source = "effect Ask { [3,3] ask() -> i64; } pub fn helper() -> i64 / Ask { Ask::ask() } pub fn main() -> i64 { handle { let value = helper(); value + 1 } { Ask::ask(k) => k(20) + k(21) + k(22) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(entry.instructions.iter().any(|instruction| matches!(
        instruction,
        VmInstruction::InstallHandler {
            continuation: VmContinuationPolicy::Replay { uses: 3 },
            ..
        }
    )));
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::ResumeReturn { .. }))
            .count(),
        3
    );
    assert_eq!(artifact.run_i64().unwrap(), 66);
}

#[test]
fn service_replays_a_heterogeneous_operation_result_across_a_call() {
    let source = "effect Read { [2,2] read() -> Text; } pub fn helper() -> i64 / Read { let text = Read::read(); 40 } pub fn main() -> i64 { handle { let value = helper(); value + 1 } { Read::read(k) => k(\"one\") + k(\"two\") } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(entry.instructions.iter().any(|instruction| matches!(
        instruction,
        VmInstruction::InstallHandler {
            resume_type: VmType::Text,
            continuation: VmContinuationPolicy::Replay { uses: 2 },
            ..
        }
    )));
    assert_eq!(artifact.run_i64().unwrap(), 82);
}

#[test]
fn service_replays_distinct_generic_operations_across_a_direct_call() {
    let source = "effect Console<T> { [2,2] read() -> T; [2,2] write(value: T) -> i64; } pub fn helper() -> i64 / Console<Text> { let text = Console<Text>::read(); Console<Text>::write(text) } pub fn main() -> i64 { handle { let value = helper(); value + 1 } { Console<Text>::read(k) => k(\"one\") + k(\"two\"); Console<Text>::write(value, k) => k(10) + k(20) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    let frames = entry
        .instructions
        .iter()
        .filter_map(|instruction| match instruction {
            VmInstruction::InstallHandler {
                effect_arguments,
                operation,
                resume_type,
                continuation: VmContinuationPolicy::Replay { uses: 2 },
                target,
                ..
            } => Some((
                effect_arguments.clone(),
                *operation,
                resume_type.clone(),
                *target,
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        frames.len(),
        2,
        "each operation needs its own replay frame: {entry:#?}"
    );
    assert_eq!(frames[0].0, vec![VmGenericArgument::Type(VmType::Text)]);
    assert_eq!(frames[1].0, vec![VmGenericArgument::Type(VmType::Text)]);
    assert_eq!(frames[0].1, 0);
    assert_eq!(frames[0].2, VmType::Text);
    assert_eq!(frames[1].1, 1);
    assert_eq!(frames[1].2, VmType::I64);
    assert_ne!(
        frames[0].3, frames[1].3,
        "operations must not share a handler entry"
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::ResumeReturn { .. }))
            .count(),
        4,
        "both exact two-shot operations must resume through their own replay frames"
    );
    assert_eq!(artifact.run_i64().unwrap(), 64);
}

#[test]
fn service_replays_generic_operation_payloads_through_generic_call_frames() {
    let source = "effect Exchange<T> { [2,2] exchange<U>(value: T, reply: U) -> U; } pub fn leaf<T, U>(value: T, reply: U) -> U / Exchange<T> { Exchange<T>::exchange<U>(value, reply) } pub fn relay<T, U>(value: T, reply: U) -> U / Exchange<T> { leaf(value, reply) } pub fn main() -> Text { handle relay(7, \"payload\") { Exchange<i64>::exchange<Text>(_, reply, k) => k(reply) + k(reply) } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("generic operation instances must retain payload types across replayed calls");
    let artifact = outcome.artifact.expect("build must publish a VM artifact");
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(entry.instructions.iter().any(|instruction| matches!(
        instruction,
        VmInstruction::InstallHandler {
            effect_arguments,
            resume_type: VmType::Text,
            continuation: VmContinuationPolicy::Replay { uses: 2 },
            ..
        } if effect_arguments.as_slice() == [VmGenericArgument::Type(VmType::I64)]
    )));
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::ResumeReturn { .. }))
            .count(),
        2,
        "each replayed generic continuation must return to the handler clause"
    );
    assert_eq!(artifact.run_text().unwrap(), "payloadpayload");
}

#[test]
fn service_replays_distinct_generic_operations_through_a_function_value() {
    let source = "effect Console<T> { [2,2] read() -> T; [2,2] write(value: T) -> i64; } pub fn helper() -> i64 / Console<Text> { let text = Console<Text>::read(); Console<Text>::write(text) } pub fn main() -> i64 { let operation = helper; handle { let value = operation(); value + 1 } { Console<Text>::read(k) => k(\"one\") + k(\"two\"); Console<Text>::write(value, k) => k(10) + k(20) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
        "the captured function value must survive into the protected call"
    );
    let frames = entry
        .instructions
        .iter()
        .filter_map(|instruction| match instruction {
            VmInstruction::InstallHandler {
                effect_arguments,
                operation,
                resume_type,
                continuation: VmContinuationPolicy::Replay { uses: 2 },
                target,
                ..
            } => Some((
                effect_arguments.clone(),
                *operation,
                resume_type.clone(),
                *target,
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        frames.len(),
        2,
        "each indirect operation needs a replay frame"
    );
    assert_eq!(frames[0].0, vec![VmGenericArgument::Type(VmType::Text)]);
    assert_eq!(frames[1].0, vec![VmGenericArgument::Type(VmType::Text)]);
    assert_eq!((frames[0].1, &frames[0].2), (0, &VmType::Text));
    assert_eq!((frames[1].1, &frames[1].2), (1, &VmType::I64));
    assert_ne!(frames[0].3, frames[1].3);
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::ResumeReturn { .. }))
            .count(),
        4
    );
    assert_eq!(artifact.run_i64().unwrap(), 64);
}

#[test]
fn service_replays_an_ordered_refutable_operation_matrix_across_calls() {
    for (indirect, source) in [
        (
            false,
            "effect Ask { [2,2] ask(value: i64) -> i64; } pub fn helper(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn main() -> i64 { handle helper(40) { Ask::ask(0) with k => k(1) + k(2); Ask::ask(value) with k => k(value) + k(value + 1) } }",
        ),
        (
            true,
            "effect Ask { [2,2] ask(value: i64) -> i64; } pub fn helper(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn main() -> i64 { let operation = helper; handle operation(40) { Ask::ask(0) with k => k(1) + k(2); Ask::ask(value) with k => k(value) + k(value + 1) } }",
        ),
    ] {
        let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
        assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
        let artifact = outcome.artifact.unwrap();
        let program = decode_program(&artifact.canonical_bytes()).unwrap();
        let entry = program.functions.get(&program.entry).unwrap();
        assert_eq!(
            entry
                .instructions
                .iter()
                .filter(|instruction| matches!(instruction, VmInstruction::ResumeReturn { .. }))
                .count(),
            4,
        );
        assert!(
            entry
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::PatternTest { .. }))
        );
        assert_eq!(
            entry
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
            indirect,
        );
        assert_eq!(artifact.run_i64().unwrap(), 81);
    }
}

#[test]
fn service_forwards_a_nested_partial_replay_matrix_to_an_outer_replay_handler() {
    for (indirect, source) in [
        (
            false,
            "effect Read { [2,2] read(value: Text) -> Text; } pub fn helper() -> i64 / Read { let text = Read::read(\"payload\"); 40 } pub fn partial() -> i64 / Read { handle helper() { Read::read(\"no\") with k => k(\"x\") + k(\"y\") } } pub fn main() -> i64 { handle { let value = partial(); value + 1 } { Read::read(value) with k => k(\"one\") + k(\"two\") } }",
        ),
        (
            true,
            "effect Read { [2,2] read(value: Text) -> Text; } pub fn helper() -> i64 / Read { let text = Read::read(\"payload\"); 40 } pub fn partial() -> i64 / Read { handle helper() { Read::read(\"no\") with k => k(\"x\") + k(\"y\") } } pub fn main() -> i64 { let action = partial; handle { let value = action(); value + 1 } { Read::read(value) with k => k(\"one\") + k(\"two\") } }",
        ),
    ] {
        let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
        assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
        let artifact = outcome.artifact.unwrap();
        let program = decode_program(&artifact.canonical_bytes()).unwrap();
        assert!(program.functions.values().any(|function| {
            function
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::Forward))
        }));
        let entry = program.functions.get(&program.entry).unwrap();
        assert_eq!(
            entry
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
            indirect
        );
        assert!(
            entry
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::ResumeReturn { .. }))
        );
        assert_eq!(artifact.run_i64().unwrap(), 82);
    }
}

#[test]
fn service_replays_an_indirect_cross_call_continuation_with_resume_return() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn leaf() -> i64 / Ask { Ask::ask() } pub fn helper() -> i64 / Ask { leaf() } pub fn main() -> i64 { let operation = helper; handle { let value = operation(); let mutable = value; mutable = mutable + 1; mutable } { Ask::ask(k) => k(20) + k(21) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
        "the replayed protected computation must retain its function-value call"
    );
    assert!(
        entry.instructions.iter().any(|instruction| matches!(
            instruction,
            VmInstruction::InstallHandler {
                continuation: VmContinuationPolicy::Replay { uses: 2 },
                ..
            }
        )),
        "the function-value call must retain the same replayable frame contract"
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::ResumeReturn { .. }))
            .count(),
        2
    );
    assert_eq!(artifact.run_i64().unwrap(), 43);
}

#[test]
fn service_rejects_an_underused_cross_call_replay_contract() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn leaf() -> i64 / Ask { Ask::ask() } pub fn helper() -> i64 / Ask { leaf() } pub fn main() -> i64 { handle { let value = helper(); let mutable = value; mutable = mutable + 1; mutable } { Ask::ask(k) => k(20) } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("one resume unexpectedly satisfied an exact two-shot cross-call contract")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6005"),
        "missing cross-call replay quantity diagnostic: {diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5012"),
        "missing structured cross-call continuation-use diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_an_underused_indirect_generic_resumption() {
    let source = "effect Ask<T> { [2,2] ask(value: T) -> T; } pub fn helper<T>(value: T) -> T / Ask<T> { let copy = value; Ask<T>::ask(copy) } pub fn main() -> i64 { handle helper(41) { Ask<i64>::ask(value) with k => k(value) } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("underused indirect generic resumption was accepted")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5012"),
        "missing indirect generic quantity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_composes_an_intercepted_helper_call_with_normal_completion() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn helper(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn main() -> i64 { handle helper(41) { result => result + 1, Ask::ask(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_intercepts_a_terminal_performance_reached_through_a_helper() {
    let source = "effect Stop { stop(value: i64) -> !; } pub fn helper(value: i64) -> i64 / Stop { Stop::stop(value) } pub fn main() -> i64 { handle helper(42) { Stop::stop(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_intercepts_a_nontransparent_terminal_callee_through_a_vm_frame() {
    let source = "effect Stop { stop(value: i64) -> !; } pub fn leaf(value: i64) -> ! / Stop { Stop::stop(value) } pub fn helper(value: i64) -> ! / Stop { let copied = value; leaf(copied) } pub fn main() -> i64 { handle helper(42) { Stop::stop(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Call { .. })),
        "terminal helper must remain a normal VM call"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. })),
        "caller must retain a terminal handler frame across the call"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Cancel)),
        "terminal arm must cancel the suspended frame before returning"
    );
    assert!(
        program
            .functions
            .values()
            .any(
                |function| function.instructions.iter().any(|instruction| matches!(
                    instruction,
                    VmInstruction::Perform { dst, .. }
                        if function.registers[*dst as usize] == VmType::Unit
                ))
            ),
        "the terminal performance's Never result must encode as the VM bottom/unit register"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_intercepts_an_indirect_terminal_callee_through_a_vm_frame() {
    let source = "effect Stop { stop(value: i64) -> !; } pub fn leaf(value: i64) -> ! / Stop { Stop::stop(value) } pub fn helper(value: i64) -> ! / Stop { let copied = value; leaf(copied) } pub fn main() -> i64 { let operation = helper; handle operation(42) { Stop::stop(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
        "terminal function values must preserve their indirect VM call"
    );
    assert!(
        entry.instructions.iter().any(|instruction| matches!(
            instruction,
            VmInstruction::InstallHandler {
                continuation: VmContinuationPolicy::Terminal,
                ..
            }
        )),
        "the indirect terminal call must carry explicit terminal frame evidence"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_cancels_an_outward_effect_call_through_a_vm_frame() {
    let source = "effect Ask { [0, 1] ask(value: i64) -> i64; } pub fn leaf(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn helper(value: i64) -> i64 / Ask { let copied = value + 0; leaf(copied) } pub fn main() -> i64 { handle helper(40) { Ask::ask(_) with _ => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Call { .. })),
        "the cancelled helper must remain an ordinary VM call"
    );
    assert!(
        entry.instructions.iter().any(|instruction| matches!(
            instruction,
            VmInstruction::InstallHandler {
                continuation: VmContinuationPolicy::Consume,
                ..
            }
        )),
        "the caller must install a consuming cancellation frame"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Cancel)),
        "the cancellation arm must consume the cross-call suspended frame"
    );
    assert!(
        program.functions.values().any(|function| function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Perform { .. }))),
        "the leaf's outward effect must remain a real VM Perform"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_cancels_an_indirect_outward_effect_call_through_a_vm_frame() {
    let source = "effect Ask { [0, 1] ask(value: i64) -> i64; } pub fn helper(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn main() -> i64 { let operation = helper; handle operation(40) { Ask::ask(_) with _ => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
        "the cancelled function value must retain its indirect VM call"
    );
    assert!(entry.instructions.iter().any(|instruction| matches!(
        instruction,
        VmInstruction::InstallHandler {
            continuation: VmContinuationPolicy::Consume,
            ..
        }
    )));
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_cancellation_frame_keeps_the_operation_result_type_across_a_call() {
    let source = "effect Read { [0, 1] read() -> Text; } pub fn helper() -> i64 / Read { let ignored = Read::read(); 0 } pub fn main() -> i64 { handle helper() { Read::read() with _ => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(entry.instructions.iter().any(|instruction| matches!(
        instruction,
        VmInstruction::InstallHandler {
            resume_type: VmType::Text,
            continuation: VmContinuationPolicy::Consume,
            ..
        }
    )));
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_cancels_a_generic_multi_operation_call_through_distinct_vm_frames() {
    let source = "effect Console<T> { [0, 1] read(value: T) -> Text; [0, 1] write(value: T) -> i64; } pub fn helper<T>(value: T) -> i64 / Console<T> { let text = Console<T>::read(value); Console<T>::write(value) } pub fn main() -> i64 { handle helper(40) { Console<i64>::read(_) with _ => 42, Console<i64>::write(_) with _ => 0 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    let frames = entry
        .instructions
        .iter()
        .filter_map(|instruction| match instruction {
            VmInstruction::InstallHandler {
                effect_arguments,
                operation,
                resume_type,
                continuation: VmContinuationPolicy::Consume,
                ..
            } if effect_arguments.as_slice() == [VmGenericArgument::Type(VmType::I64)] => {
                Some((*operation, resume_type))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(frames, vec![(0, &VmType::Text), (1, &VmType::I64)]);
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::UninstallHandler))
            .count(),
        2,
        "normal completion must clean up every installed cancellation frame"
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::Cancel))
            .count(),
        2,
        "each distinct operation frame needs its own cancellation target"
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_cancels_a_generic_operation_instance_through_generic_call_frames() {
    let source = "effect Exchange<T> { [0,1] exchange<U>(value: T, reply: U) -> U; } pub fn leaf<T, U>(value: T, reply: U) -> U / Exchange<T> { Exchange<T>::exchange<U>(value, reply) } pub fn relay<T, U>(value: T, reply: U) -> U / Exchange<T> { leaf(value, reply) } pub fn main() -> Text { handle relay(7, \"payload\") { Exchange<i64>::exchange<Text>(_, _) with _ => \"cancelled\" } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("generic cancellation must preserve its concrete operation result type");
    let artifact = outcome.artifact.expect("build must publish a VM artifact");
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(entry.instructions.iter().any(|instruction| matches!(
        instruction,
        VmInstruction::InstallHandler {
            effect_arguments,
            resume_type: VmType::Text,
            continuation: VmContinuationPolicy::Consume,
            ..
        } if effect_arguments.as_slice() == [VmGenericArgument::Type(VmType::I64)]
    )));
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Cancel)),
        "the cancellation clause must consume the suspended generic call frame"
    );
    assert_eq!(artifact.run_text().unwrap(), "cancelled");
}

#[test]
fn service_cancels_a_generic_multi_operation_function_value_through_vm_frames() {
    let source = "effect Console<T> { [0, 1] read(value: T) -> Text; [0, 1] write(value: T) -> i64; } pub fn helper<T>(value: T) -> i64 / Console<T> { let text = Console<T>::read(value); Console<T>::write(value) } pub fn main() -> i64 { let operation = helper; handle operation(40) { Console<i64>::read(_) with _ => 42, Console<i64>::write(_) with _ => 0 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CallIndirect { .. })),
        "the generic function value must retain its dynamic call boundary"
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. }))
            .count(),
        2
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_a_forged_missing_multi_operation_cancellation_cleanup() {
    let source = "effect Console { [0, 1] read() -> Text; [0, 1] write() -> i64; } pub fn helper() -> i64 / Console { let text = Console::read(); Console::write() } pub fn main() -> i64 { handle helper() { Console::read() with _ => 42, Console::write() with _ => 0 } }";
    let artifact = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap();
    let mut forged = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = forged.functions.get_mut(&forged.entry).unwrap();
    let cleanup = entry
        .instructions
        .iter()
        .rposition(|instruction| matches!(instruction, VmInstruction::UninstallHandler))
        .expect("generated multi-operation caller has cleanup");
    entry.instructions.remove(cleanup);
    forged.fingerprint = forged.computed_fingerprint();
    assert!(
        decode_and_verify_program(&encode_program(&forged)).is_err(),
        "a forged caller cannot return with a live cancellation frame"
    );
}

#[test]
fn service_resumption_binds_payloads_before_entering_a_nonempty_continuation() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(41); value + 1 } { Ask::ask(seed) with k => k(seed) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_projects_nested_record_binders_before_entering_continuation() {
    let source = "pub struct Ticket { serial: i64 } effect Ask { [1,1] ask(ticket: Ticket) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(Ticket { serial: 41 }); value + 1 } { Ask::ask(Ticket { serial: serial }) with k => k(serial) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_projects_tuple_binders_before_entering_continuation() {
    let source = "effect Ask { [1,1] ask(pair: (i64, i64)) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask((40, 1)); value + 1 } { Ask::ask((left, right)) with k => k(left + right) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_selects_ordered_payload_patterns_before_a_nonempty_continuation() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(1); value + 1 } { Ask::ask(1) with k => k(40); Ask::ask(_) with k => k(41) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_resumption_uses_the_irrefutable_fallback_after_a_payload_pattern_miss() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(2); value + 1 } { Ask::ask(1) with k => k(40); Ask::ask(_) with k => k(41) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn generic_vm_calls_preserve_nominal_argument_relationships() {
    let source = "pub struct Box<T> { value: T } pub fn identity<T>(value: Box<T>) -> Box<T> { value } pub fn main() -> Box<i64> { identity(Box { value: 42 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(
        outcome.artifact.unwrap().run_record_i64().unwrap(),
        vec![42]
    );
}

#[test]
fn generic_vm_calls_instantiate_binders_nested_inside_array_types() {
    let source = "pub fn identity<T>(value: Array<T>) -> Array<T> { value } pub fn main() -> Array<i64> { identity([42]) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_array_i64().unwrap(), vec![42]);
}

#[test]
fn check_mode_reuses_semantic_validation_without_publishing_a_vm_artifact() {
    let mut check = request("pub fn main() -> i64 { 40 + 2 }");
    check.mode = CompilationMode::Check;
    let outcome = StageZeroCompiler::new().compile(check).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert!(outcome.artifact.is_none());
    assert!(outcome.bootstrap_manifest.is_none());
}

#[test]
fn bootstrap_stages_record_path_free_manifests_and_prove_convergence() {
    let source = "pub fn main() -> i64 { 40 + 2 }";
    let mut stage_one = request(source);
    stage_one.build.compiler = Digest::of_bytes(b"rust-seed");
    stage_one.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 1,
        producer: Digest::of_bytes(b"rust-seed"),
        optimization_level: 2,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: None,
    });
    let compiler = StageZeroCompiler::new();
    let first = compiler.compile(stage_one).unwrap();
    let first_manifest = first.bootstrap_manifest.unwrap();
    let first_artifact = first.artifact.unwrap();
    first_manifest
        .validate_verified_artifact(&first_artifact)
        .unwrap();
    let mut forged_byte_commitment = first_manifest.clone();
    forged_byte_commitment.artifact_bytes = Digest::of_bytes(b"forged-stage-one-bytes");
    assert!(matches!(
        forged_byte_commitment.validate_verified_artifact(&first_artifact),
        Err(BootstrapArtifactCompatibilityError::ArtifactBytesMismatch { .. })
    ));
    assert_eq!(first_artifact.run_i64().unwrap(), 42);

    let mut stage_two = request(source);
    stage_two.build.compiler = first_manifest.artifact;
    stage_two.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 2,
        producer: first_manifest.artifact,
        optimization_level: 2,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: Some(first_manifest.artifact),
    });
    let second = compiler.compile(stage_two).unwrap();
    let second_manifest = second.bootstrap_manifest.unwrap();
    assert_ne!(first_manifest.world, second_manifest.world);
    assert_eq!(
        first_manifest.source_semantics,
        second_manifest.source_semantics
    );
    assert_eq!(first_manifest.codegen, second_manifest.codegen);
    first_manifest
        .compare_convergence(&second_manifest)
        .unwrap();

    let mut stage_three = request(source);
    stage_three.build.compiler = second_manifest.artifact;
    stage_three.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 3,
        producer: second_manifest.artifact,
        optimization_level: 2,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: Some(second_manifest.artifact),
    });
    let third_manifest = compiler
        .compile(stage_three)
        .unwrap()
        .bootstrap_manifest
        .unwrap();
    second_manifest
        .compare_convergence(&third_manifest)
        .unwrap();
    assert_eq!(second_manifest.artifact, third_manifest.artifact);
    assert_eq!(
        second_manifest.artifact_bytes,
        third_manifest.artifact_bytes
    );
}

#[test]
fn bootstrap_stage_rejects_a_nonconvergent_expected_artifact() {
    let mut request = request("pub fn main() -> i64 { 42 }");
    request.build.compiler = Digest::of_bytes(b"not-this-program");
    request.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 2,
        producer: Digest::of_bytes(b"not-this-program"),
        optimization_level: 2,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: Some(Digest::of_bytes(b"not-this-program")),
    });
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("nonconvergent bootstrap unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G7012")
    );
}

#[test]
fn bootstrap_convergence_failure_discards_emission_session_staging() {
    // The mismatch is diagnosed only after MIR selection, VM emission, and
    // verification.  It is therefore the strongest observable rollback
    // witness for the EmissionSession boundary: no package/interface or
    // artifact dependency product may publish from that abandoned request.
    let compiler = StageZeroCompiler::new();
    let mut nonconvergent = request("pub fn main() -> i64 { 42 }");
    nonconvergent.build.compiler = Digest::of_bytes(b"emission-session-rollback");
    nonconvergent.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 2,
        producer: Digest::of_bytes(b"emission-session-rollback"),
        optimization_level: 2,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: Some(Digest::of_bytes(b"emission-session-rollback")),
    });
    let failed_revision = compiler.import_revision(nonconvergent, None).unwrap();
    let failed_session = compiler.open_session(failed_revision).unwrap();
    let error = compiler.compile_session(&failed_session).unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G7012")
    );
    assert!(compiler.dependency_traces(failed_revision).is_empty());
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 0);

    // A later request must start from fresh staging and publish normally.
    let succeeding_revision = compiler
        .import_revision(request("pub fn main() -> i64 { 42 }"), None)
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(succeeding_revision)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn bootstrap_manifest_rejects_mismatched_codegen_even_when_artifacts_match() {
    let mut first = request("pub fn main() -> i64 { 42 }");
    first.build.compiler = Digest::of_bytes(b"seed");
    first.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 1,
        producer: Digest::of_bytes(b"seed"),
        optimization_level: 1,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: None,
    });
    let first = StageZeroCompiler::new()
        .compile(first)
        .unwrap()
        .bootstrap_manifest
        .unwrap();
    let mut second = request("pub fn main() -> i64 { 42 }");
    second.build.compiler = first.artifact;
    second.target = "different-vm".into();
    second.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 2,
        producer: first.artifact,
        optimization_level: 1,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: Some(first.artifact),
    });
    let second = StageZeroCompiler::new()
        .compile(second)
        .unwrap()
        .bootstrap_manifest
        .unwrap();
    assert!(matches!(
        first.compare_convergence(&second),
        Err(BootstrapConvergenceError::CodegenInputMismatch { .. })
    ));
}

#[test]
fn bootstrap_convergence_rejects_skipped_or_substituted_successors() {
    let common = |stage: BootstrapStage, artifact: Digest| BootstrapManifest {
        schema: BOOTSTRAP_MANIFEST_SCHEMA,
        stage,
        world: Digest::of_bytes(b"stage-world"),
        source_semantics: Digest::of_bytes(b"stage-source"),
        codegen: Digest::of_bytes(b"stage-codegen"),
        artifact,
        artifact_bytes: Digest::of_bytes(b"stage-artifact-bytes"),
    };
    let stage_one_artifact = Digest::of_bytes(b"stage-one-artifact");
    let first = common(
        BootstrapStage {
            ordinal: 1,
            producer: Digest::of_bytes(b"rust-seed"),
            optimization_level: 2,
            limits: BootstrapLimits::new(4, 16 * 1024),
            expected_artifact: None,
        },
        stage_one_artifact,
    );
    let substituted = common(
        BootstrapStage {
            ordinal: 2,
            producer: Digest::of_bytes(b"substituted-stage-one"),
            optimization_level: 2,
            limits: BootstrapLimits::new(4, 16 * 1024),
            expected_artifact: Some(Digest::of_bytes(b"substituted-stage-one")),
        },
        stage_one_artifact,
    );
    assert!(matches!(
        first.compare_convergence(&substituted),
        Err(BootstrapConvergenceError::ProducerMismatch { expected, found })
            if expected == stage_one_artifact && found == Digest::of_bytes(b"substituted-stage-one")
    ));

    let skipped = common(
        BootstrapStage {
            ordinal: 3,
            producer: stage_one_artifact,
            optimization_level: 2,
            limits: BootstrapLimits::new(4, 16 * 1024),
            expected_artifact: Some(stage_one_artifact),
        },
        stage_one_artifact,
    );
    assert!(matches!(
        first.compare_convergence(&skipped),
        Err(BootstrapConvergenceError::StageOrderMismatch {
            earlier: 1,
            later: 3
        })
    ));

    let mut byte_distinct = substituted;
    byte_distinct.stage.ordinal = 2;
    byte_distinct.stage.producer = stage_one_artifact;
    byte_distinct.stage.expected_artifact = Some(stage_one_artifact);
    byte_distinct.artifact_bytes = Digest::of_bytes(b"different-canonical-envelope");
    assert!(matches!(
        first.compare_convergence(&byte_distinct),
        Err(BootstrapConvergenceError::ArtifactBytesMismatch { .. })
    ));
}

#[test]
fn bootstrap_manifests_round_trip_canonically_and_reject_corruption() {
    let manifest = BootstrapManifest {
        schema: BOOTSTRAP_MANIFEST_SCHEMA,
        stage: BootstrapStage {
            ordinal: 2,
            producer: Digest::of_bytes(b"stage-one-artifact"),
            optimization_level: 2,
            limits: BootstrapLimits::new(4, 16 * 1024),
            expected_artifact: Some(Digest::of_bytes(b"stage-one-artifact")),
        },
        world: Digest::of_bytes(b"world"),
        source_semantics: Digest::of_bytes(b"source"),
        codegen: Digest::of_bytes(b"codegen"),
        artifact: Digest::of_bytes(b"artifact"),
        artifact_bytes: Digest::of_bytes(b"artifact-bytes"),
    };
    let bytes = manifest.encode().unwrap();
    assert_eq!(BootstrapManifest::decode(&bytes).unwrap(), manifest);
    assert_eq!(
        manifest.encode().unwrap(),
        bytes,
        "manifest encoding is not canonical"
    );

    let mut byte_commitment = manifest.clone();
    byte_commitment.artifact_bytes = Digest::of_bytes(b"forged-byte-commitment");
    let verified = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { 42 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(matches!(
        byte_commitment.validate_verified_artifact(&verified),
        Err(BootstrapArtifactCompatibilityError::ArtifactMismatch { .. })
    ));

    let mut wrong_magic = bytes.clone();
    wrong_magic[0] ^= 1;
    assert!(matches!(
        BootstrapManifest::decode(&wrong_magic),
        Err(BootstrapManifestError::InvalidMagic)
    ));
    assert!(matches!(
        BootstrapManifest::decode(&bytes[..bytes.len() - 1]),
        Err(BootstrapManifestError::Truncated)
    ));
    // A hostile manifest cannot relabel a stage-two record as an unbound
    // successor by merely removing the optional-artifact payload. Decode
    // validates the reconstructed stage before returning evidence.
    let expected_tag_offset = BOOTSTRAP_MANIFEST_MAGIC.len()
        + std::mem::size_of::<u32>()
        + std::mem::size_of::<u32>()
        + 32
        + std::mem::size_of::<u8>()
        + std::mem::size_of::<u32>()
        + std::mem::size_of::<u64>();
    let mut unbound_successor = bytes.clone();
    assert_eq!(unbound_successor[expected_tag_offset], 1);
    unbound_successor[expected_tag_offset] = 0;
    unbound_successor.drain(expected_tag_offset + 1..expected_tag_offset + 1 + 32);
    assert!(matches!(
        BootstrapManifest::decode(&unbound_successor),
        Err(BootstrapManifestError::InvalidStage {
            reason: "non-seed stages must pin their predecessor artifact"
        })
    ));
    let mut trailing = bytes;
    trailing.push(0);
    assert!(matches!(
        BootstrapManifest::decode(&trailing),
        Err(BootstrapManifestError::TrailingBytes)
    ));

    let mut invalid = manifest;
    invalid.schema += 1;
    assert!(matches!(
        invalid.encode(),
        Err(BootstrapManifestError::UnsupportedSchema { .. })
    ));
}

#[test]
fn service_lowers_tuple_construction_through_the_verified_vm() {
    let outcome = StageZeroCompiler::new()
        .compile(request("pub fn main() -> (i64, i64) { (40, 2) }"))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(
        outcome.artifact.unwrap().run_tuple_i64().unwrap(),
        vec![40, 2]
    );
}

#[test]
fn service_lowers_typed_array_literals_through_the_verified_vm() {
    let outcome = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Array<i64> { [40, 2] }"))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(
        outcome.artifact.unwrap().run_array_i64().unwrap(),
        vec![40, 2]
    );
}

#[test]
fn empty_array_literals_infer_their_element_type_from_the_result_contract() {
    let outcome = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Array<i64> { [] }"))
        .unwrap();
    assert_eq!(
        outcome.artifact.unwrap().run_array_i64().unwrap(),
        Vec::<i64>::new()
    );
}

#[test]
fn service_lowers_generic_struct_construction_through_the_verified_vm() {
    let source = "pub struct Pair<T> { left: T, right: T } pub fn main() -> Pair<i64> { Pair { left: 40, right: 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(
        outcome.artifact.unwrap().run_record_i64().unwrap(),
        vec![40, 2]
    );
}

#[test]
fn service_resolves_empty_braced_nominals_without_stealing_callable_blocks() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub struct Empty {} pub fn main() -> Empty { Empty {} }",
        ))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_record_i64().unwrap(), vec![]);

    let ordinary = StageZeroCompiler::new()
        .compile(request(
            "pub fn choose(body: () -> ()) -> () { body() } pub fn main() -> () { choose {} }",
        ))
        .unwrap();
    ordinary.artifact.unwrap().run_unit().unwrap();
}

#[test]
fn service_constructs_empty_named_enum_payloads_from_the_same_braced_surface() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub enum Token { End {} } pub fn main() -> Token { Token::End {} }",
        ))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_enum_i64().unwrap(), vec![]);
}

#[test]
fn service_lowers_struct_field_projection_through_the_verified_vm() {
    let source = "pub struct Pair<T> { left: T, right: T } pub fn main() -> i64 { Pair { left: 40, right: 2 }.left + Pair { left: 40, right: 2 }.right }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_generic_tuple_enum_construction_through_the_verified_vm() {
    let source =
        "pub enum Choice<T> { Value(T), Empty } pub fn main() -> Choice<i64> { Choice::Value(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_enum_i64().unwrap(), vec![42]);
}

#[test]
fn service_lowers_named_enum_payload_construction_through_the_verified_vm() {
    let source = "pub enum Result<T> { Ok(T), Err { code: i64 } } pub fn main() -> Result<i64> { Result::Err { code: 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_enum_i64().unwrap(), vec![42]);
}

#[test]
fn service_lowers_validated_radix_integer_literals() {
    let outcome = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { 0x2a + 0b0 }"))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_every_remaining_typed_integer_literal_across_generic_calls() {
    // Each case crosses a separately materialized generic call boundary.
    macro_rules! literal_case {
        ($ty:ident, $value:literal, $run:ident, $instruction:pat) => {{
            let artifact = StageZeroCompiler::new()
                .compile(request(&format!(
                    "pub fn relay<T>(value: T) -> T {{ value }} pub fn literal() -> {} {{ {} }} pub fn main() -> {} {{ relay(literal()) }}",
                    stringify!($ty),
                    stringify!($value),
                    stringify!($ty),
                )))
                .unwrap_or_else(|diagnostics| panic!("{} literal: {diagnostics:#?}", stringify!($ty)))
                .artifact
                .expect("build must publish a VM artifact");
            assert_eq!(artifact.$run().unwrap(), $value);
            let program = decode_program(&artifact.canonical_bytes()).unwrap();
            assert!(program.functions.values().any(|function| {
                function
                    .instructions
                    .iter()
                    .any(|instruction| matches!(instruction, $instruction))
            }));
            artifact
        }};
    }

    literal_case!(
        u16,
        65535,
        run_u16,
        VmInstruction::ConstU16 { value: 65535, .. }
    );
    literal_case!(
        usize,
        18446744073709551615,
        run_usize,
        VmInstruction::ConstUsize {
            value: u64::MAX,
            ..
        }
    );
    literal_case!(
        u128,
        340282366920938463463374607431768211455,
        run_u128,
        VmInstruction::ConstU128 {
            value: u128::MAX,
            ..
        }
    );
    literal_case!(i8, 127, run_i8, VmInstruction::ConstI8 { value: 127, .. });
    literal_case!(
        i16,
        32767,
        run_i16,
        VmInstruction::ConstI16 { value: 32767, .. }
    );
    literal_case!(
        i32,
        2147483647,
        run_i32,
        VmInstruction::ConstI32 {
            value: i32::MAX,
            ..
        }
    );
    literal_case!(
        isize,
        9223372036854775807,
        run_isize,
        VmInstruction::ConstIsize {
            value: i64::MAX,
            ..
        }
    );
    let artifact = literal_case!(
        i128,
        170141183460469231731687303715884105727,
        run_i128,
        VmInstruction::ConstI128 {
            value: i128::MAX,
            ..
        }
    );

    let mut forged = decode_program(&artifact.canonical_bytes()).unwrap();
    let (function_key, constant) = forged
        .functions
        .iter()
        .find_map(|(key, function)| {
            function
                .instructions
                .iter()
                .find_map(|instruction| match instruction {
                    VmInstruction::ConstI128 { dst, .. } => Some((*key, *dst)),
                    _ => None,
                })
        })
        .expect("typed i128 literal is present in the decoded artifact");
    forged
        .functions
        .get_mut(&function_key)
        .expect("selected constant belongs to the decoded artifact")
        .registers[constant as usize] = VmType::I64;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(
        decode_and_verify_program(&encode_program(&forged)).is_err(),
        "a typed integer immediate cannot publish into a register of another width"
    );
}

#[test]
fn service_parses_checks_and_executes_typed_constant_initializers() {
    let source = "const forty: i64 = 40; const two: i64 = 2; pub fn main() -> i64 { forty + two }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_public_constants_from_another_module() {
    let root = "mod math; pub fn main() -> i64 { math::answer }";
    let child = "pub const answer: i64 = 42;";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_constant_initializer_cycles_before_vm_emission() {
    let source =
        "const first: i64 = second; const second: i64 = first; pub fn main() -> i64 { first }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("constant cycle unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G7008")
    );
}

#[test]
fn service_executes_frozen_top_level_value_initializer_calls() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } let answer = add_one(41); pub fn main() -> i64 { answer }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_freezes_constructor_top_level_value_initializers() {
    let source =
        "pub enum Result { Err(()) } let None = Result::Err(()); pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_generalizes_polymorphic_top_level_value_initializers() {
    let source = "pub enum Result<T, E> { Ok(T), Err(E) } type Option<T> = Result<T, ()>; let None = Result::Err(()); pub fn no_number() -> Option<i64> { None } pub fn no_text() -> Option<Text> { None } pub fn main() -> i64 { handle no_number() { Result::Ok(_) => 0, Result::Err(_) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_accepts_canonical_boolean_value_initializer_spellings() {
    let source = "pub fn __g1_bool_true() -> Bool { true } pub fn __g1_bool_false() -> Bool { false } let true = __g1_bool_true(); let false = __g1_bool_false(); pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_public_top_level_value_initializers_across_modules() {
    let root = "mod math; let answer = math::value(); pub fn main() -> i64 { answer }";
    let child = "pub fn value() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_exported_top_level_value_initializers_from_another_module() {
    let root = "mod math; pub fn main() -> i64 { math::answer }";
    let child = "pub fn value() -> i64 { 42 } pub let answer = value();";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_bad_top_level_value_initializer_call_arguments() {
    let source = "pub fn identity(value: i64) -> i64 { value } let broken = identity(true); pub fn main() -> i64 { 42 }";
    let error = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4107"),
        "initializer call argument mismatch was accepted: {:#?}",
        error.diagnostics()
    );
}

#[test]
fn service_rejects_effectful_top_level_value_initializers() {
    let source =
        "effect Ask { ask() -> i64; } let answer = Ask::ask(); pub fn main() -> i64 { 42 }";
    let error = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "effectful top-level initializer was accepted: {:#?}",
        error.diagnostics()
    );
}

#[test]
fn service_executes_transparent_type_alias_contracts() {
    let source = "type Count = i64; pub fn add_two(value: Count) -> Count { value + 2 } pub fn main() -> Count { add_two(40) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_normalizes_transparent_aliases_imported_from_another_module() {
    let root = "mod types; use types::Count; pub fn add_two(value: Count) -> Count { value + 2 } pub fn main() -> Count { add_two(40) }";
    let child = "pub type Count = i64;";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(root, &[("types", child)]))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_freezes_alias_spelled_delayed_effect_projection_identity() {
    let source = "type Count = i64; trait Capability<T> { type Effects: EffectRow; } struct Value {} impl Capability<i64> for Value { type Effects = {}; } struct Carrier<e: EffectRow> {} type Wrapped<e: EffectRow> = Carrier<e>; pub fn worker(value: Wrapped<{ <Value as Capability<Count>>::Effects }>) -> i64 { 0 } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_effectful_callback_aliases_with_their_sealed_effect_row() {
    let source = "effect Ask { [1,1] ask() -> i64; } type Callback = () -> i64 / Ask; pub fn leaf() -> i64 / Ask { Ask::ask() } pub fn relay(callback: Callback) -> i64 / Ask { callback() } pub fn main() -> i64 { handle relay(leaf) { Ask::ask() with k => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_forwarding_an_effectful_callback_alias_through_an_empty_row() {
    let source = "effect Ask { [1,1] ask() -> i64; } type Callback = () -> i64 / Ask; pub fn leaf() -> i64 / Ask { Ask::ask() } pub fn relay(callback: Callback) -> i64 { callback() } pub fn main() -> i64 { relay(leaf) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("effectful callback alias escaped through an empty outward row")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "missing outward-effect diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_lowers_f64_arithmetic_and_typed_calls_to_the_verified_vm() {
    let source = "pub fn double(value: f64) -> f64 { value * 2.0 } pub fn main() -> f64 { double(20.5) + 1.0 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_f64().unwrap(), 42.0);
}

#[test]
fn manifest_bound_f32_leaf_accepts_contextual_decimal_literals_through_vm() {
    // Decimal source literals receive the parameter's width.  The trusted
    // f32 leaf then proves that this path retains f32 rather than falling
    // back to the default f64 literal representation.
    let source = "fn __g1_f32_add(left: f32, right: f32) -> f32 { () } pub fn main() -> f32 { __g1_f32_add(40.5, 1.5) }";
    let mut input = request(source);
    input.runtime_manifest = Some(int_runtime_manifest(
        PrimitiveRole::parse_selector_name("f32-add").unwrap(),
        "__g1_f32_add",
    ));
    let artifact = StageZeroCompiler::new()
        .compile(input)
        .expect("contextual f32 literals must reach the trusted f32 primitive")
        .artifact
        .expect("build must publish a VM artifact");
    assert_eq!(artifact.run_f32().unwrap(), 42.0);
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    assert!(program.functions.values().any(|function| {
        function.instructions.iter().any(|instruction| {
            matches!(instruction, VmInstruction::ConstF32 { .. })
        })
    }));
}

#[test]
fn source_float_arithmetic_canonicalizes_runtime_nan_results() {
    let artifact = StageZeroCompiler::new()
        .compile(request("pub fn main() -> f64 { 0.0 / 0.0 }"))
        .unwrap()
        .artifact
        .unwrap();
    let value = artifact.run_f64().unwrap();
    assert!(value.is_nan());
    assert_eq!(value.to_bits(), 0x7ff8_0000_0000_0000);
}

#[test]
fn source_rejects_decimal_f64_literals_that_overflow_to_an_unspelled_infinity() {
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request("pub fn main() -> f64 { 1e9999 }"))
    else {
        panic!("an overflowing decimal literal unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6003"),
        "{diagnostics:#?}"
    );
}

#[test]
fn verified_vm_executes_division_and_remainder_without_host_panics() {
    let integer = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { 84 / 2 % 43 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(integer.run_i64().unwrap(), 42);
    let float = StageZeroCompiler::new()
        .compile(request("pub fn main() -> f64 { 84.0 / 2.0 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(float.run_f64().unwrap(), 42.0);
    let zero = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { 1 / 0 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(matches!(
        zero.run_i64(),
        Err(VmArtifactError::DivisionByZero)
    ));
}

#[test]
fn service_lowers_source_defined_prefix_numeric_operators() {
    let integer = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { -40 + +2 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(integer.run_i64().unwrap(), -38);
    let float = StageZeroCompiler::new()
        .compile(request("pub fn main() -> f64 { -40.5 + +82.5 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(float.run_f64().unwrap(), 42.0);
}

#[test]
fn service_lowers_boolean_prefix_negation() {
    let artifact = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { !false }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(artifact.run_bool().unwrap());
}

#[test]
fn service_lowers_char_literals_and_scalar_comparisons() {
    let character = StageZeroCompiler::new()
        .compile(request("pub fn main() -> char { '\\u{1f980}' }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(character.run_char().unwrap(), '🦀');

    let comparison = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { 'a' < 'z' }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(comparison.run_bool().unwrap());

    let boolean = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { true != false }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(boolean.run_bool().unwrap());
}

#[test]
fn service_lowers_shared_text_handles_and_text_equality() {
    let text = StageZeroCompiler::new()
        .compile(request(
            "pub fn echo(value: Text) -> Text { value } pub fn main() -> Text { echo(\"hello, \\u{1f980}\") }",
        ))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(text.run_text().unwrap(), "hello, 🦀");

    let equality = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { \"same\" == \"same\" }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(equality.run_bool().unwrap());

    let concatenated = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Text { \"hello, \" + \"world\" }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(concatenated.run_text().unwrap(), "hello, world");
}

#[test]
fn service_lowers_empty_blocks_to_verified_unit_values() {
    let artifact = StageZeroCompiler::new()
        .compile(request(
            "pub fn noop() -> () { } pub fn main() -> () { noop() }",
        ))
        .unwrap()
        .artifact
        .unwrap();
    artifact.run_unit().unwrap();
}

#[test]
fn prefix_operators_reject_incompatible_operand_types_before_mir() {
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request("pub fn main() -> Bool { -true }"))
    else {
        panic!("invalid prefix operand unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4117")
    );
}

#[test]
fn service_lowers_bool_literals_and_typed_numeric_comparisons() {
    let integer = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { 20 + 22 == 42 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(integer.run_bool().unwrap());
    let float = StageZeroCompiler::new()
        .compile(request(
            "pub fn below(value: f64) -> Bool { value < 2.0 } pub fn main() -> Bool { below(1.5) }",
        ))
        .unwrap()
        .artifact
        .unwrap();
    assert!(float.run_bool().unwrap());
    let literal = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { true }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(literal.run_bool().unwrap());
}

#[test]
fn service_lowers_immediately_invoked_typed_closures_with_captures() {
    let source =
        "pub fn main() -> i64 { let value = 40; ((extra: i64) -> i64 { value + extra })(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn nll_releases_an_immediately_invoked_closure_capture_before_the_next_write() {
    let source = "pub fn main() -> i64 { let value = 1; ((extra: i64) -> i64 { value + extra })(1); value = 42; value }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("an immediately invoked closure must not retain its capture after returning");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_infers_and_lowers_immediately_invoked_compact_closures() {
    let source = "pub fn main() -> i64 { { extra => extra + 2 }(40) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_uses_parameter_expectations_for_compact_closure_arguments() {
    let source = "pub fn invoke(callback: (i64) -> i64) -> i64 { callback(41) } pub fn main() -> i64 { invoke({ value => value + 1 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_lexically_bound_closures_with_creation_time_captures() {
    let source = "pub fn main() -> i64 { let value = 40; let add = (extra: i64) -> i64 { value + extra }; add(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn lexical_closure_calls_rebind_parameters_on_each_invocation() {
    let source = "pub fn main() -> i64 { let value = 40; let add = (extra: i64) -> i64 { value + extra }; add(1) + add(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn lexical_closure_captures_are_stable_across_later_shadowing() {
    let source = "pub fn main() -> i64 { let value = 40; let add = (extra: i64) -> i64 { value + extra }; let value = 100; add(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn nested_closures_preserve_the_source_environment_brand_and_capture_layout() {
    let source = "pub fn main() -> i64 { let base = 30; let outer = (first: i64) -> i64 { let inner = (second: i64) -> i64 { base + first + second }; inner(2) }; outer(10) }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("nested closures must retain their source-owned environments while lifting");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn nested_closures_forward_unique_and_move_capture_authority_without_shadowing() {
    let unique = "pub fn main() -> i64 { let value = 40; let outer = () -> i64 { let inner = () -> i64 { value = value + 2; value }; inner() }; outer() }";
    let outcome = StageZeroCompiler::new()
        .compile(request(unique))
        .expect("nested unique capture must be forwarded to the lifted inner callable");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let moved = "pub fn main() -> i64 { let value = 42; let outer = () -> i64 { let inner = () -> i64 { move value }; inner() }; outer() }";
    let outcome = StageZeroCompiler::new()
        .compile(request(moved))
        .expect("nested move capture must be forwarded to the lifted inner callable");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let value = 42; let outer = () -> i64 { let inner = () -> i64 { move value }; inner() }; value }",
        ))
    else {
        panic!("outer source remained usable after a transitively moved capture")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "missing transitive moved-capture diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_executes_sealed_capture_post_states_and_rejects_their_moved_source_use() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let value = 42; let take = () -> i64 { move value }; take() }",
        ))
        .expect("sealed move capture must lower through the VM");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let value = 42; let take = () -> i64 { move value }; value }",
        ))
    else {
        panic!("use after a moved capture unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "missing moved-capture post-state diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn callables_cross_direct_call_boundaries_and_remain_indirectly_invocable() {
    let source = "pub fn make(value: i64) -> (i64) -> i64 { (extra: i64) -> i64 { value + extra } } pub fn main() -> i64 { make(40)(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn generic_closure_values_preserve_indirect_call_contracts() {
    let generic = "pub fn identity<T>(value: T) -> T { let invoke = (input: T) -> T { input }; invoke(value) } pub fn main() -> i64 { identity(42) }";
    let outcome = StageZeroCompiler::new()
        .compile(request(generic))
        .expect("generic closure value must materialize before its indirect call");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_generic_value_captures_in_returned_closures() {
    let source = "pub fn capture<T>(value: T) -> () -> T { () -> T { value } } pub fn main() -> i64 { capture(42)() }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("a returned closure must specialize its captured generic value");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_nested_generic_value_captures_in_returned_closures() {
    let source = "pub fn capture<T>(value: T) -> () -> () -> T { () -> () -> T { () -> T { value } } } pub fn main() -> i64 { capture(42)()() }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("nested returned closures must specialize their captured generic value");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn callable_values_cross_record_and_return_indirect_boundaries() {
    let source = "pub struct Holder { callback: (i64) -> i64 } pub fn make(value: i64) -> Holder { Holder { callback: (input: i64) -> i64 { value + input } } } pub fn main() -> i64 { let holder = make(40); holder.callback(2) }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("record-stored returned closure must retain its indirect-call environment");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_source_lexing_failures_through_the_release_root() {
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request("pub fn main() -> i64 { 0b102 }"))
    else {
        panic!("malformed numeric literal unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G1008")
    );
}

#[test]
fn service_never_emits_a_release_artifact_from_recovered_body_or_core() {
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request("pub fn main() -> i64 { unresolved }"))
    else {
        panic!("recovered Typed Core unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G7007")
    );
}

#[test]
fn service_emits_a_verified_deterministic_program_for_direct_helper_calls() {
    let source = "pub fn forty() -> i64 { 40 } pub fn main() -> i64 { forty() + 2 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_passes_header_typed_arguments_through_verified_vm_frames() {
    let source =
        "pub fn add_two(value: i64) -> i64 { value + 2 } pub fn main() -> i64 { add_two(40) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn verified_vm_program_enforces_explicit_runtime_call_depth_limits() {
    let source = "pub fn recurse() -> i64 { recurse() } pub fn main() -> i64 { recurse() }";
    let artifact = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap();
    assert!(matches!(
        artifact.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 4,
            max_handler_depth: 4_096,
            max_instructions: 100,
            ..VmExecutionLimits::default()
        }),
        Err(VmArtifactError::CallDepthLimit { limit: 4 })
    ));
}

#[test]
fn verified_vm_program_enforces_explicit_handler_depth_limits() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(40) { Ask::ask(0) => 0 } } { Ask::ask(value) => value + 2 } }";
    let artifact = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap();
    assert!(matches!(
        artifact.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 100,
            max_handler_depth: 1,
            max_instructions: 100,
            ..VmExecutionLimits::default()
        }),
        Err(VmArtifactError::HandlerDepthLimit { limit: 1 })
    ));
}

#[test]
fn verified_vm_program_enforces_explicit_instruction_limits() {
    let source = "pub fn recurse() -> i64 { recurse() } pub fn main() -> i64 { recurse() }";
    let artifact = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap();
    assert!(matches!(
        artifact.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 100,
            max_handler_depth: 4_096,
            max_instructions: 2,
            ..VmExecutionLimits::default()
        }),
        Err(VmArtifactError::InstructionLimit { limit: 2 })
    ));
}

#[test]
fn service_compiles_explicit_external_modules_from_the_request_source_world() {
    let root = "mod math; pub fn main() -> i64 { math::add_two(40) }";
    let child = "pub fn add_two(value: i64) -> i64 { value + 2 }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_routes_cross_module_open_effect_row_forwarding_through_root_handler() {
    let root = "mod math; use math::Trace; use math::forward; use math::leaf; pub fn main() -> i64 { handle forward<{Trace}>(leaf) { Trace::note() with k => k(42) } }";
    let child = "pub effect Trace { [1,1] note() -> i64; } pub fn leaf() -> i64 / Trace { Trace::note() } pub fn forward<e: EffectRow>(call: () -> i64 / {| e}) -> i64 / {| e} { call() }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .expect("the root handler must receive a concrete residual row from a child module");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_links_public_dependency_package_interfaces_and_bodies() {
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::answer; pub fn main() -> i64 { answer() }",
            "math@0.1.0",
            "pub fn answer() -> i64 { 42 }",
        ))
        .expect("a supplied dependency package must participate in root import resolution");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_normalizes_hyphenated_dependency_package_names_into_source_module_aliases() {
    // Package identity remains the manifest key (`math-lib@…`), while source
    // paths use the deterministic language-level module alias (`math_lib`).
    // Exercise the complete package/interface/body/VM route so this cannot
    // regress into a header-only spelling normalization.
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math_lib::answer; pub fn main() -> i64 { answer() }",
            "math-lib@0.1.0",
            "pub fn answer() -> i64 { 42 }",
        ))
        .expect("a hyphenated dependency package must be reachable by its normalized alias");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_recursive_hyphenated_dependency_facades_with_generic_effect_gats() {
    // Both package identities contain hyphens, so their source aliases differ
    // from their manifest keys. The two public interfaces import each other:
    // `effects_lib` owns the effect and reexports the trait, while
    // `traits_lib` imports the effect to define the selected generic GAT row.
    let mut request = request(
        "use effects_lib::{Capability, Trace}; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: Capability<i64>::relay(0, 41) }; Trace<i64>::note(packet.value) } pub fn main() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("effects-lib@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub use traits_lib::Child as Capability;".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("traits-lib@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use effects_lib::Trace; pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {}".as_slice(),
    ));
    let mut reordered = request.clone();
    reordered.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(first)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("a package import cycle unexpectedly reached VM materialization");
    };
    let Err(grandiose_stage0::ServiceError::Failed(second)) =
        StageZeroCompiler::new().compile(reordered)
    else {
        panic!("source enumeration changed package-cycle rejection into success");
    };
    assert!(
        first.iter().any(|diagnostic| diagnostic.code == "G3321"),
        "missing package-cycle diagnostic: {first:#?}"
    );
    assert!(
        first.iter().all(|diagnostic| diagnostic.code == "G3321"),
        "package-cycle input must fail before later semantic products: {first:#?}"
    );
    assert_eq!(
        first.len(),
        2,
        "each reciprocal package import must retain its source diagnostic"
    );
    assert_eq!(first, second, "package-cycle diagnostics must be canonical");
}

#[test]
fn service_seals_dag_hrtb_alias_interfaces_before_private_facade_transactions() {
    let root = "use top_facade::*; pub fn apply(callback: Relay<i64>) -> i64 / Audit<i64> { let value = 41; let result = callback(&value); *result } pub fn effect_value() -> i64 { handle apply(relay) { Audit<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let ambiguous_root = "use left_facade::*; use right_facade::*; pub fn main() -> i64 { 1 ** 2 }";
    let provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Effects<U>: EffectRow; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Effects<U> = {Trace<U>}; } impl Child<i64> for i64 {} pub type Callback<U> = for<'a> (&'a i64) -> &'a i64 / { <i64 as Child<i64>>::Effects<U> }; pub fn relay<'a>(value: &'a i64) -> &'a i64 / Trace<i64> { Trace<i64>::note(*value); value }";
    let world = |root: &str,
                 providers: Vec<(&str, &str)>,
                 left_alias: &str,
                 right_alias: &str,
                 private_left_aliases: bool| {
        let mut input = request(root);
        for (package, source) in providers {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                source.as_bytes(),
            ));
        }
        let left = if private_left_aliases {
            format!(
                "use {left_alias}::{{Callback as Relay, Child as Capability, Combine as Operator, Trace as Audit}}; pub use {left_alias}::*;"
            )
        } else {
            format!(
                "pub use {left_alias}::{{Callback as Relay, Child as Capability, Combine as Operator, Trace as Audit}}; pub use {left_alias}::*;"
            )
        };
        for (package, source) in [
            ("left-facade@0.1.0", left),
            (
                "right-facade@0.1.0",
                format!(
                    "pub use {right_alias}::{{Callback as Relay, Child as Capability, Combine as Operator, Trace as Audit}}; pub use {right_alias}::*;"
                ),
            ),
            (
                "top-facade@0.1.0",
                "pub use left_facade::{Audit, Capability, Operator, Relay}; pub use right_facade::*;"
                    .to_owned(),
            ),
        ] {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                source.into_bytes(),
            ));
        }
        input
    };

    let public = world(
        root,
        vec![("semantic-core@0.1.0", provider)],
        "semantic_core",
        "semantic_core",
        false,
    );
    let compiler = StageZeroCompiler::new();
    let parent = compiler.import_revision(public.clone(), None).unwrap();
    let first = compiler
        .compile_revision(parent)
        .expect("same provider identities must deduplicate across DAG facade paths")
        .artifact
        .unwrap();
    assert_eq!(first.run_i64().unwrap(), 50);
    let top = DependencyNode::Interface(ModuleKey {
        package: PackageKey("top-facade@0.1.0".into()),
        path: "crate".into(),
    });
    let published_top = compiler
        .dependency_trace(parent, &top)
        .expect("the public top facade must freeze");
    let mut reordered_public = public.clone();
    reordered_public.sources.reverse();
    let replay = compiler.import_revision(reordered_public, Some(parent)).unwrap();
    assert_eq!(replay, parent);
    let replay_artifact = compiler.compile_revision(replay).unwrap().artifact.unwrap();
    assert_eq!(first.fingerprint(), replay_artifact.fingerprint());
    assert_eq!(first.canonical_bytes(), replay_artifact.canonical_bytes());
    let cached = compiler.interface_cache_stats();

    let ambiguous = world(
        ambiguous_root,
        vec![("alpha-core@0.1.0", provider), ("beta-core@0.1.0", provider)],
        "alpha_core",
        "beta_core",
        false,
    );
    let mut ambiguous_reordered = ambiguous.clone();
    ambiguous_reordered.sources.reverse();
    let first_ambiguity = StageZeroCompiler::new()
        .compile(ambiguous)
        .expect_err("distinct same-named providers must not deduplicate by spelling");
    let second_ambiguity = StageZeroCompiler::new()
        .compile(ambiguous_reordered)
        .expect_err("source order cannot resolve distinct provider aliases");
    assert!(
        first_ambiguity
            .diagnostics()
            .iter()
            .any(|diagnostic| matches!(diagnostic.code, "G3314" | "G3318" | "G4111")),
        "missing distinct-provider public-interface ambiguity: {:#?}",
        first_ambiguity.diagnostics()
    );
    assert_eq!(first_ambiguity.diagnostics(), second_ambiguity.diagnostics());

    let private = world(
        root,
        vec![("semantic-core@0.1.0", provider)],
        "semantic_core",
        "semantic_core",
        true,
    );
    let child = compiler.import_revision(private.clone(), Some(parent)).unwrap();
    let error = compiler
        .compile_session(&compiler.open_session(child).unwrap())
        .expect_err("a private left alias cannot satisfy an unchanged public top facade");
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| matches!(diagnostic.code, "G3317" | "G3326")),
        "missing private facade alias authority diagnostic: {:#?}",
        error.diagnostics()
    );
    assert_eq!(compiler.interface_cache_stats(), cached);
    assert!(compiler.dependency_traces(child).is_empty());
    assert_eq!(compiler.dependency_trace(parent, &top), Some(published_top));
    let mut private_reordered = private;
    private_reordered.sources.reverse();
    assert_eq!(
        error.diagnostics(),
        StageZeroCompiler::new()
            .compile(private_reordered)
            .expect_err("source order cannot make a private alias public")
            .diagnostics(),
        "private facade alias diagnostics must be canonical"
    );

    let repaired = compiler.import_revision(public, Some(parent)).unwrap();
    assert_eq!(repaired, parent);
    let repaired_artifact = compiler.compile_revision(repaired).unwrap().artifact.unwrap();
    assert_eq!(first.canonical_bytes(), repaired_artifact.canonical_bytes());
    assert_eq!(repaired_artifact.run_i64().unwrap(), 50);
}

#[test]
fn service_revises_generic_operator_facade_cache_identities_transactionally() {
    let root = "use left_facade::*; use right_facade::{Callback as RightRelay, Child as RightCapability, Trace as RightTrace}; pub fn left_call(callback: Callback<i64>) -> i64 / { <i64 as Child<i64>>::Effects<i64> } { callback(0, 41) } pub fn right_call(callback: RightRelay<i64>) -> i64 / { <i64 as RightCapability<i64>>::Effects<i64> } { callback(0, 41) } pub fn left_worker() -> i64 / Trace<i64> { Trace<i64>::note(left_call(Child<i64>::relay)) } pub fn right_worker() -> i64 / RightTrace<i64> { RightTrace<i64>::note(right_call(RightCapability<i64>::relay)) } pub fn left_value() -> i64 { handle left_worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn right_value() -> i64 { handle right_worker() { RightTrace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + left_value() + right_value() }";
    let ambiguity_root = "use left_facade::*; use right_facade::*; pub fn main() -> i64 { 1 ** 2 }";
    let public = |fixity: &str| format!("pub {fixity} 30 **; pub trait Combine<T> {{ **(left: T, right: T) -> T; }} impl Combine<i64> for i64 {{ **(left: i64, right: i64) -> i64 {{ left - right }} }} pub effect Trace<T> {{ [1,1] note(value: T) -> i64; }} pub trait Parent<T> {{ type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> i64 / {{ <Self as Parent<T>>::Effects<U> }}; }} pub trait Child<T>: Parent<T> {{}} impl Parent<i64> for i64 {{ type Effects<U> = {{Trace<U>}}; fn relay<U>(receiver: i64, value: U) -> i64 / {{Trace<U>}} {{ Trace<U>::note(value) }} }} impl Child<i64> for i64 {{}} pub type Callback<U> = (i64, U) -> i64 / {{ <i64 as Child<i64>>::Effects<U> }};");
    let private = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> i64 / { <Self as Parent<T>>::Effects<U> }; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> i64 / { <i64 as Child<i64>>::Effects<U> };";
    let world = |root: &str, providers: Vec<(&str, String)>, left: &str, right: &str| {
        let mut input = request(root);
        for (package, source) in providers { input.sources.push(SourceInput::new(PackageKey(package.into()), LogicalPath::parse("src/lib.glorious").unwrap(), source.into_bytes())); }
        for (package, alias) in [("left-facade@0.1.0", left), ("right-facade@0.1.0", right)] {
            input.sources.push(SourceInput::new(PackageKey(package.into()), LogicalPath::parse("src/lib.glorious").unwrap(), format!("pub use {alias}::{{Callback, Child, Combine, Trace}}; pub use {alias}::*;").into_bytes()));
        }
        input
    };
    let compiler = StageZeroCompiler::new();
    let initial = world(root, vec![("semantic-core@0.1.0", public("infixl"))], "semantic_core", "semantic_core");
    let parent = compiler.import_revision(initial.clone(), None).unwrap();
    let first = compiler.compile_revision(parent).unwrap().artifact.unwrap();
    assert_eq!(first.run_i64().unwrap(), 91);
    let mut reordered = initial.clone(); reordered.sources.reverse();
    let replay = compiler.import_revision(reordered, Some(parent)).unwrap(); assert_eq!(replay, parent);
    let replay_artifact = compiler.compile_revision(replay).unwrap().artifact.unwrap();
    assert_eq!(first.fingerprint(), replay_artifact.fingerprint()); assert_eq!(first.canonical_bytes(), replay_artifact.canonical_bytes());
    let cached = compiler.interface_cache_stats();
    let left_node = DependencyNode::Interface(ModuleKey { package: PackageKey("left-facade@0.1.0".into()), path: "crate".into() });
    let left_parent = compiler.dependency_trace(parent, &left_node).unwrap();

    let ambiguous = world(ambiguity_root, vec![("alpha-core@0.1.0", public("infixl")), ("beta-core@0.1.0", public("infixr"))], "alpha_core", "beta_core");
    let mut ambiguous_reordered = ambiguous.clone(); ambiguous_reordered.sources.reverse();
    let ambiguous_first = StageZeroCompiler::new().compile(ambiguous).expect_err("distinct provider operator identities must be ambiguous");
    let ambiguous_second = StageZeroCompiler::new().compile(ambiguous_reordered).expect_err("source order cannot choose a provider fixity");
    assert!(ambiguous_first.diagnostics().iter().any(|d| matches!(d.code, "G3314" | "G3318" | "G4111")));
    assert_eq!(ambiguous_first.diagnostics(), ambiguous_second.diagnostics());

    let rejected_world = world(root, vec![("semantic-core@0.2.0", private.into())], "semantic_core", "semantic_core");
    let rejected = compiler.import_revision(rejected_world.clone(), Some(parent)).unwrap();
    let error = compiler.compile_session(&compiler.open_session(rejected).unwrap()).expect_err("private provider aliases must reject the child revision");
    assert!(error.diagnostics().iter().any(|d| matches!(d.code, "G3304" | "G3310" | "G3315" | "G3317" | "G3326")));
    assert!(error.diagnostics().iter().all(|d| d.code != "G4111"));
    assert_eq!(compiler.interface_cache_stats(), cached); assert!(compiler.dependency_traces(rejected).is_empty());
    assert_eq!(compiler.dependency_trace(parent, &left_node), Some(left_parent.clone()));
    let mut rejected_reordered = rejected_world; rejected_reordered.sources.reverse();
    assert_eq!(error.diagnostics(), StageZeroCompiler::new().compile(rejected_reordered).expect_err("private rejection is order-invariant").diagnostics());

    let repaired = compiler.import_revision(world(root, vec![("semantic-core@0.2.0", public("infixr"))], "semantic_core", "semantic_core"), Some(parent)).unwrap();
    let second = compiler.compile_revision(repaired).unwrap().artifact.unwrap();
    assert_eq!(second.run_i64().unwrap(), 95); assert_ne!(first.canonical_bytes(), second.canonical_bytes());
    let left_repaired = compiler.dependency_trace(repaired, &left_node).unwrap(); assert_ne!(left_parent.fingerprint, left_repaired.fingerprint);
    assert!(compiler.interface_cache_stats().misses > cached.misses);
}

#[test]
fn service_isolates_illegal_hyphenated_package_cycles_from_legal_hrtb_module_sccs() {
    let legal_root = "use legal_facade::*; pub fn apply(callback: Callback<i64>) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); *result } pub fn effect_value() -> i64 { handle apply(relay) { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let illegal_root = "use legal_facade::*; use effects_lib::Callback as RejectedCallback; pub fn apply(callback: Callback<i64>) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); *result } pub fn effect_value() -> i64 { handle apply(relay) { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Effects<U>: EffectRow; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Effects<U> = {Trace<U>}; } impl Child<i64> for i64 {} pub type Callback<U> = for<'a> (&'a i64) -> &'a i64 / { <i64 as Child<i64>>::Effects<U> }; pub fn relay<'a>(value: &'a i64) -> &'a i64 / Trace<i64> { Trace<i64>::note(*value); value }";
    let legal_world = |root: &str| {
        let mut input = request(root);
        for (package, path, source) in [
            ("semantic-core@0.1.0", "src/lib.glorious", provider),
            (
                "legal-facade@0.1.0",
                "src/lib.glorious",
                "pub mod left; pub mod right; pub use crate::left::*; pub use crate::right::*;",
            ),
            (
                "legal-facade@0.1.0",
                "src/left/left.glorious",
                "pub use crate::right::*; pub use semantic_core::{Callback, Combine, Trace, relay}; pub use semantic_core::*;",
            ),
            (
                "legal-facade@0.1.0",
                "src/right/right.glorious",
                "pub use crate::left::*; pub use semantic_core::{Callback, Combine, Trace, relay}; pub use semantic_core::*;",
            ),
        ] {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse(path).unwrap(),
                source.as_bytes(),
            ));
        }
        input
    };
    let illegal_sources = [
        (
            "effects-lib@0.1.0",
            "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub use traits_lib::{Callback, Child as Capability};",
        ),
        (
            "traits-lib@0.1.0",
            "pub use effects_lib::{Combine, Trace}; pub use effects_lib::*; pub trait Parent<T> { type Effects<U>: EffectRow; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Effects<U> = {Trace<U>}; } impl Child<i64> for i64 {} pub type Callback<U> = for<'a> (&'a i64) -> &'a i64 / { <i64 as Child<i64>>::Effects<U> };",
        ),
    ];

    let compiler = StageZeroCompiler::new();
    let public = legal_world(legal_root);
    let parent = compiler.import_revision(public.clone(), None).unwrap();
    let artifact = compiler
        .compile_revision(parent)
        .expect("the legal shared-provider module SCC must compile through HRTB callback dispatch")
        .artifact
        .unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 50);
    let cached_parent = compiler.interface_cache_stats();
    let provider_interface = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-core@0.1.0".into()),
        path: "crate".into(),
    });
    let mut published = Vec::new();
    for path in ["crate", "crate::left", "crate::right"] {
        let node = DependencyNode::Interface(ModuleKey {
            package: PackageKey("legal-facade@0.1.0".into()),
            path: path.into(),
        });
        let trace = compiler
            .dependency_trace(parent, &node)
            .expect("each legal module-SCC interface must publish");
        assert!(trace.dependencies.contains(&provider_interface));
        published.push((node, trace));
    }

    let mut illegal = legal_world(illegal_root);
    for (package, source) in illegal_sources {
        illegal.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let child = compiler.import_revision(illegal.clone(), Some(parent)).unwrap();
    let error = compiler
        .compile_session(&compiler.open_session(child).unwrap())
        .expect_err("the separate hyphenated package SCC must fail before body publication");
    assert!(
        error.diagnostics().iter().all(|diagnostic| diagnostic.code == "G3321"),
        "only package-cycle diagnostics may escape the illegal SCC: {:#?}",
        error.diagnostics()
    );
    assert!(
        error.diagnostics().len() >= 2,
        "the reciprocal package edges must each retain a cycle diagnostic"
    );
    assert_eq!(compiler.interface_cache_stats(), cached_parent);
    assert!(compiler.dependency_traces(child).is_empty());
    for (node, trace) in &published {
        assert_eq!(compiler.dependency_trace(parent, node), Some(trace.clone()));
    }
    let mut reordered = illegal;
    reordered.sources.reverse();
    assert_eq!(
        error.diagnostics(),
        StageZeroCompiler::new()
            .compile(reordered)
            .expect_err("source ordering cannot legalize a package SCC")
            .diagnostics(),
        "illegal package-SCC diagnostics must be canonical"
    );

    let repaired = compiler.import_revision(public, Some(parent)).unwrap();
    assert_eq!(
        repaired, parent,
        "repairing by removing the illegal package SCC must reuse only the legal request world"
    );
    let replay = compiler.compile_revision(repaired).unwrap().artifact.unwrap();
    assert_eq!(artifact.fingerprint(), replay.fingerprint());
    assert_eq!(artifact.canonical_bytes(), replay.canonical_bytes());
    assert_eq!(replay.run_i64().unwrap(), 50);
    assert_eq!(compiler.interface_cache_stats().misses, cached_parent.misses);
    for (node, trace) in published {
        let replay_trace = compiler
            .dependency_trace(repaired, &node)
            .expect("the repaired legal SCC interfaces must remain available");
        assert_eq!(replay_trace.fingerprint, trace.fingerprint);
        assert_eq!(replay_trace.dependencies, trace.dependencies);
    }
}

#[test]
fn service_executes_three_package_diamond_gat_effect_facades_canonically() {
    // The provider sits at the point of a package DAG: both hyphenated
    // facades publicly re-export its generic effect and child-trait GAT
    // contract.  The root imports both globs, so equivalent identities must
    // deduplicate rather than become source-order-dependent ambiguities.
    let root = "use left_facade::*; use right_facade::*; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: Capability<i64>::relay(0, 41) }; Trace<i64>::note(packet.value) } pub fn main() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } }";
    let provider = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {}";
    let facade = "pub use effect_core::{Child as Capability, Trace};";
    let mut request = request(root);
    for (package, source) in [
        ("effect-core@0.1.0", provider),
        ("left-facade@0.1.0", facade),
        ("right-facade@0.1.0", facade),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let first = StageZeroCompiler::new()
        .compile(request.clone())
        .expect("a package-DAG facade diamond must preserve provider identities");
    let mut reordered = request;
    reordered.sources.reverse();
    let second = StageZeroCompiler::new()
        .compile(reordered)
        .expect("package-DAG artifact identity must not depend on source enumeration");
    assert!(first.diagnostics.is_empty(), "{:#?}", first.diagnostics);
    assert!(second.diagnostics.is_empty(), "{:#?}", second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 43);
    assert_eq!(second.run_i64().unwrap(), 43);
}

#[test]
fn service_rejects_private_generic_effects_through_three_package_diamond_facades() {
    let mut request = request("pub fn main() -> i64 { 42 }");
    for (package, source) in [
        (
            "effect-core@0.1.0",
            "effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Effects<U>: EffectRow; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Effects<U> = {Trace<U>}; } impl Child<i64> for i64 {}",
        ),
        (
            "left-facade@0.1.0",
            "pub use effect_core::{Child as Capability, Trace};",
        ),
        (
            "right-facade@0.1.0",
            "pub use effect_core::{Child as Capability, Trace};",
        ),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let mut reordered = request.clone();
    reordered.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("a private generic effect unexpectedly leaked through a package diamond");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "missing private-authority diagnostic: {diagnostics:#?}"
    );
    let Err(grandiose_stage0::ServiceError::Failed(reordered_diagnostics)) =
        StageZeroCompiler::new().compile(reordered)
    else {
        panic!("source enumeration changed private-authority rejection into success");
    };
    assert_eq!(
        diagnostics, reordered_diagnostics,
        "private-authority diagnostics must be canonical across package ordering"
    );
}

#[test]
fn service_keeps_same_spelled_generic_diamond_facades_provider_distinct_through_vm() {
    // The providers deliberately publish the same source spellings.  The
    // facade aliases make both visible to the root, which must retain their
    // declaration identities rather than unify by text while selecting GAT
    // rows and dispatching each generic effect.
    let root = "use left_facade::{Capability as LeftCapability, Trace as LeftTrace}; use right_facade::{Capability as RightCapability, Trace as RightTrace}; pub struct LeftPacket { value: <i64 as LeftCapability<i64>>::Item<i64> } pub struct RightPacket { value: <i64 as RightCapability<i64>>::Item<i64> } pub fn left_worker() -> i64 / LeftTrace<i64> { let packet = LeftPacket { value: LeftCapability<i64>::relay(0, 41) }; LeftTrace<i64>::note(packet.value) } pub fn right_worker() -> i64 / RightTrace<i64> { let packet = RightPacket { value: RightCapability<i64>::relay(0, 41) }; RightTrace<i64>::note(packet.value) } pub fn left_value() -> i64 { handle left_worker() { LeftTrace<i64>::note(value) with k => k(value + 1) } } pub fn right_value() -> i64 { handle right_worker() { RightTrace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { left_value() + right_value() }";
    let provider = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } effect Hidden<T> { [1,1] hide(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {}";
    let mut request = request(root);
    for (package, source) in [
        ("alpha-core@0.1.0", provider),
        ("beta-core@0.1.0", provider),
        (
            "left-facade@0.1.0",
            "pub use alpha_core::{Child as Capability, Trace};",
        ),
        (
            "right-facade@0.1.0",
            "pub use beta_core::{Child as Capability, Trace};",
        ),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let first = StageZeroCompiler::new()
        .compile(request.clone())
        .expect("same-spelled provider identities must remain distinct through the VM");
    let mut reordered = request;
    reordered.sources.reverse();
    let second = StageZeroCompiler::new()
        .compile(reordered)
        .expect("provider identity cannot depend on source enumeration");
    assert!(first.diagnostics.is_empty(), "{:#?}", first.diagnostics);
    assert!(second.diagnostics.is_empty(), "{:#?}", second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 86);
    assert_eq!(second.run_i64().unwrap(), 86);
}

#[test]
fn service_reports_same_spelled_distinct_provider_diamond_aliases_as_ambiguous() {
    let mut request = request(
        "use left_facade::*; use right_facade::*; pub fn worker() -> i64 / Trace<i64> { Capability<i64>::relay(0, 41) } pub fn main() -> i64 { 0 }",
    );
    let provider = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> i64 / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {}";
    for (package, source) in [
        ("alpha-core@0.1.0", provider),
        ("beta-core@0.1.0", provider),
        (
            "left-facade@0.1.0",
            "pub use alpha_core::{Child as Capability, Trace};",
        ),
        (
            "right-facade@0.1.0",
            "pub use beta_core::{Child as Capability, Trace};",
        ),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let mut reordered = request.clone();
    reordered.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(first)) = StageZeroCompiler::new().compile(request)
    else {
        panic!("same-spelled aliases from distinct providers unexpectedly resolved");
    };
    let Err(grandiose_stage0::ServiceError::Failed(second)) =
        StageZeroCompiler::new().compile(reordered)
    else {
        panic!("source ordering changed provider-identity ambiguity into success");
    };
    assert!(
        first.iter().any(|diagnostic| diagnostic.code == "G3314"),
        "missing provider-identity ambiguity diagnostic: {first:#?}"
    );
    assert_eq!(first, second, "provider-identity ambiguity must be canonical");
}

#[test]
fn service_rejects_private_same_spelled_generic_effect_reexports_in_a_provider_diamond() {
    let mut request = request("pub fn main() -> i64 { 42 }");
    let private_provider = "effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Effects<U>: EffectRow; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Effects<U> = {Trace<U>}; } impl Child<i64> for i64 {}";
    let public_provider = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Effects<U>: EffectRow; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Effects<U> = {Trace<U>}; } impl Child<i64> for i64 {}";
    for (package, source) in [
        ("alpha-core@0.1.0", private_provider),
        ("beta-core@0.1.0", public_provider),
        (
            "left-facade@0.1.0",
            "pub use alpha_core::{Child as Capability, Trace};",
        ),
        (
            "right-facade@0.1.0",
            "pub use beta_core::{Child as Capability, Trace};",
        ),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let mut reordered = request.clone();
    reordered.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(first)) = StageZeroCompiler::new().compile(request)
    else {
        panic!("a public provider unexpectedly authorized a private same-spelled reexport");
    };
    let Err(grandiose_stage0::ServiceError::Failed(second)) =
        StageZeroCompiler::new().compile(reordered)
    else {
        panic!("source ordering changed private reexport rejection into success");
    };
    assert!(
        first.iter().any(|diagnostic| diagnostic.code == "G3317"),
        "missing private provider authority diagnostic: {first:#?}"
    );
    assert_eq!(first, second, "private provider diagnostics must be canonical");
}

#[test]
fn service_executes_generic_authorized_reexport_diamond_with_operator_fixity() {
    // Both facades expose the *same* provider identities.  This is therefore
    // a valid diamond: duplicate glob paths must deduplicate the generic
    // effect/GAT contract and its re-exported fixity/trait pair together.
    let root = "use left_facade::*; use right_facade::*; pub struct Packet { value: <i64 as Child<i64>>::Item<i64> } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: Child<i64>::relay(0, 41) }; Trace<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let provider = "pub infixr 30 **; pub trait Combine { **(left: i64, right: i64) -> i64; } impl Combine for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {}";
    let mut request = request(root);
    for (package, source) in [
        ("semantic-core@0.1.0", provider),
        ("left-facade@0.1.0", "pub use semantic_core::*;"),
        ("right-facade@0.1.0", "pub use semantic_core::*;"),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let first = StageZeroCompiler::new()
        .compile(request.clone())
        .expect("authorized package facades must preserve generic effect and fixity identity");
    let mut reordered = request;
    reordered.sources.reverse();
    let second = StageZeroCompiler::new()
        .compile(reordered)
        .expect("authorized re-export artifacts must be source-order invariant");
    assert!(first.diagnostics.is_empty(), "{:#?}", first.diagnostics);
    assert!(second.diagnostics.is_empty(), "{:#?}", second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 52);
    assert_eq!(second.run_i64().unwrap(), 52);
}

#[test]
fn service_executes_multilevel_callable_alias_effect_row_and_fixity_facades() {
    let root = "use top_facade::*; pub fn call(callback: Callback<i64>) -> i64 / Trace<i64> { callback(0, 41) } pub fn effect_value() -> i64 { handle call(relay) { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let provider = "pub infixr 30 **; pub trait Combine { **(left: i64, right: i64) -> i64; } impl Combine for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub type Callback<U> = (i64, U) -> i64 / {Trace<U>}; pub fn relay<U>(receiver: i64, value: U) -> i64 / Trace<U> { Trace<U>::note(value) }";
    let mut request = request(root);
    for (package, source) in [
        ("semantic-core@0.1.0", provider),
        ("middle-facade@0.1.0", "pub use semantic_core::*;"),
        ("top-facade@0.1.0", "pub use middle_facade::*;"),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let first = StageZeroCompiler::new()
        .compile(request.clone())
        .expect("multilevel facades must retain callable aliases, rows, and fixities");
    let mut reordered = request;
    reordered.sources.reverse();
    let second = StageZeroCompiler::new()
        .compile(reordered)
        .expect("multilevel facade artifacts must not depend on source enumeration");
    assert!(first.diagnostics.is_empty(), "{:#?}", first.diagnostics);
    assert!(second.diagnostics.is_empty(), "{:#?}", second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 51);
    assert_eq!(second.run_i64().unwrap(), 51);
}

#[test]
fn service_preserves_generic_associated_items_and_callable_aliases_through_reexport_chains() {
    let root = "use top_facade::*; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn call(callback: Callback<i64>) -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: call(Capability<i64>::relay) }; Trace<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let mut request = request(root);
    for (package, source) in [
        ("semantic-core@0.1.0", provider),
        (
            "middle-facade@0.1.0",
            "pub use semantic_core::{Callback, Child as Capability, Trace}; pub use semantic_core::*;",
        ),
        ("top-facade@0.1.0", "pub use middle_facade::*;"),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let first = StageZeroCompiler::new()
        .compile(request.clone())
        .expect("re-export chains must retain generic associated item and callable alias authority");
    let mut reordered = request;
    reordered.sources.reverse();
    let second = StageZeroCompiler::new()
        .compile(reordered)
        .expect("associated-item facade artifacts must be source-order invariant");
    assert!(first.diagnostics.is_empty(), "{:#?}", first.diagnostics);
    assert!(second.diagnostics.is_empty(), "{:#?}", second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 52);
    assert_eq!(second.run_i64().unwrap(), 52);
}

#[test]
fn service_seals_generic_facade_interface_fingerprints_independent_of_source_enumeration() {
    let root = "use top_facade::*; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn call(callback: Callback<i64>) -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: call(Capability<i64>::relay) }; Trace<i64>::note(packet.value) } pub fn main() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } }";
    let provider = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let mut input = request(root);
    for (package, source) in [
        ("semantic-core@0.1.0", provider),
        (
            "middle-facade@0.1.0",
            "pub use semantic_core::{Callback, Child as Capability, Trace};",
        ),
        ("top-facade@0.1.0", "pub use middle_facade::*;"),
    ] {
        input.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }

    let compiler = StageZeroCompiler::new();
    let parent = compiler.import_revision(input.clone(), None).unwrap();
    let first = compiler
        .compile_revision(parent)
        .expect("generic facade interfaces must freeze before VM lowering");
    let mut reordered = input;
    reordered.sources.reverse();
    let child = compiler.import_revision(reordered, Some(parent)).unwrap();
    assert_eq!(
        child, parent,
        "source enumeration must normalize to the exact same immutable request world"
    );
    let second = compiler
        .compile_revision(child)
        .expect("source enumeration cannot perturb sealed public interfaces");

    let modules = [
        ("app@0.1.0", "crate"),
        ("semantic-core@0.1.0", "crate"),
        ("middle-facade@0.1.0", "crate"),
        ("top-facade@0.1.0", "crate"),
    ];
    for (package, path) in modules {
        let interface = DependencyNode::Interface(ModuleKey {
            package: PackageKey(package.into()),
            path: path.into(),
        });
        let first_trace = compiler
            .dependency_trace(parent, &interface)
            .expect("first revision must publish every package interface");
        let second_trace = compiler
            .dependency_trace(child, &interface)
            .expect("reordered revision must publish every package interface");
        assert_eq!(
            first_trace.fingerprint, second_trace.fingerprint,
            "{package} public interface fingerprint changed with source enumeration"
        );
        assert_eq!(first_trace, second_trace);
    }
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 43);
    assert_eq!(second.run_i64().unwrap(), 43);
}

#[test]
fn service_rolls_back_malformed_private_generic_facade_reexports_before_interface_publication() {
    let provider = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let mut input = request("use top_facade::*; pub fn main() -> i64 { 42 }");
    for (package, source) in [
        ("semantic-core@0.1.0", provider),
        (
            "middle-facade@0.1.0",
            "use semantic_core::{Callback, Child as Capability, Trace}; pub use semantic_core::*;",
        ),
        (
            "top-facade@0.1.0",
            "pub use middle_facade::{Callback, Capability, Trace};",
        ),
    ] {
        input.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let mut reordered = input.clone();
    reordered.sources.reverse();
    let mut diagnostics_by_order = Vec::new();
    for request in [input, reordered] {
        let compiler = StageZeroCompiler::new();
        let revision = compiler.import_revision(request, None).unwrap();
        let session = compiler.open_session(revision).unwrap();
        let error = compiler
            .compile_session(&session)
            .expect_err("a public re-export cannot elevate a private generic facade alias");
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == "G3317"),
            "missing private facade re-export diagnostic: {:#?}",
            error.diagnostics()
        );
        assert!(
            error
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.code == "G3317"),
            "interface authority must fail before body diagnostics: {:#?}",
            error.diagnostics()
        );
        assert_eq!(compiler.interface_cache_stats().hits, 0);
        assert_eq!(compiler.interface_cache_stats().misses, 0);
        assert!(
            compiler.dependency_traces(revision).is_empty(),
            "a malformed package facade must not publish partial generic interfaces"
        );
        diagnostics_by_order.push(error.diagnostics().to_vec());
    }
    assert_eq!(
        diagnostics_by_order[0], diagnostics_by_order[1],
        "private facade authority diagnostics must be canonical under source reordering"
    );
}

#[test]
fn service_discards_downstream_private_fixity_facade_staging_after_reusing_generic_upstreams() {
    let provider = "pub infixr 30 **; pub trait Combine { **(left: i64, right: i64) -> i64; } impl Combine for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let middle = "pub use semantic_core::{Callback, Child as Capability, Trace}; use semantic_core::Combine;";
    let mut upstream = request("use middle_facade::*; pub fn call(callback: Callback<i64>) -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { callback(0, 41) } pub fn main() -> i64 { handle call(Capability<i64>::relay) { Trace<i64>::note(value) with k => k(value + 1) } }");
    for (package, source) in [
        ("semantic-core@0.1.0", provider),
        ("middle-facade@0.1.0", middle),
    ] {
        upstream.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }

    let compiler = StageZeroCompiler::new();
    let parent = compiler.import_revision(upstream.clone(), None).unwrap();
    assert_eq!(
        compiler
            .compile_revision(parent)
            .expect("generic provider and authorized facade must publish first")
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    let published = compiler.interface_cache_stats();
    assert!(published.misses >= 3, "root and both upstream packages must freeze");

    let broken = "pub use middle_facade::{Callback, Capability, Combine, Trace}; pub infixr 30 **;";
    let mut failing = request("use broken_facade::*; pub fn main() -> i64 { 10 ** 3 ** 2 }");
    for source in upstream.sources.iter().skip(1) {
        failing.sources.push(source.clone());
    }
    failing.sources.push(SourceInput::new(
        PackageKey("broken-facade@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        broken.as_bytes(),
    ));
    let mut reordered = failing.clone();
    reordered.sources.reverse();
    let mut diagnostics_by_order = Vec::new();
    for input in [failing, reordered] {
        let revision = compiler.import_revision(input, Some(parent)).unwrap();
        let session = compiler.open_session(revision).unwrap();
        let error = compiler
            .compile_session(&session)
            .expect_err("a public downstream fixity cannot retain a private operator trait");
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == "G3317"),
            "missing private downstream facade authority diagnostic: {:#?}",
            error.diagnostics()
        );
        assert!(
            error
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.code == "G3317"),
            "private fixity authority must fail before body grouping: {:#?}",
            error.diagnostics()
        );
        assert_eq!(
            compiler.interface_cache_stats(),
            published,
            "failed downstream staging must not publish cache hits or misses"
        );
        assert!(
            compiler.dependency_traces(revision).is_empty(),
            "failed downstream staging must not publish any partial package interfaces"
        );
        diagnostics_by_order.push(error.diagnostics().to_vec());
    }
    assert_eq!(
        diagnostics_by_order[0], diagnostics_by_order[1],
        "downstream private fixity diagnostics must be deterministic under source reordering"
    );
}

#[test]
fn service_invalidates_generic_facade_artifacts_across_provider_versioned_fixity_updates() {
    let root = "use semantic_facade::*; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn call(callback: Callback<i64>) -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: call(Capability<i64>::relay) }; Trace<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let provider = |fixity: &str| {
        format!(
            "pub {fixity} 30 **; pub trait Combine<T> {{ **(left: T, right: T) -> T; }} impl Combine<i64> for i64 {{ **(left: i64, right: i64) -> i64 {{ left - right }} }} pub effect Trace<T> {{ [1,1] note(value: T) -> i64; }} pub trait Parent<T> {{ type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / {{ <Self as Parent<T>>::Effects<U> }}; }} pub trait Child<T>: Parent<T> {{}} impl Parent<i64> for i64 {{ type Item<U> = i64; type Effects<U> = {{Trace<U>}}; fn relay<U>(receiver: i64, value: U) -> i64 / {{Trace<U>}} {{ Trace<U>::note(value) }} }} impl Child<i64> for i64 {{}} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / {{ <i64 as Child<i64>>::Effects<U> }};"
        )
    };
    let facade = "pub use semantic_core::{Callback, Child as Capability, Trace}; pub use semantic_core::*;";
    let world = |core_package: &str, core_source: String| {
        let mut input = request(root);
        for (package, source) in [
            (core_package, core_source),
            ("semantic-facade@0.1.0", facade.into()),
        ] {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                source.as_bytes(),
            ));
        }
        input
    };

    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(world("semantic-core@0.1.0", provider("infixl")), None)
        .unwrap();
    let first = compiler
        .compile_revision(parent)
        .expect("the initial generic provider facade must compile")
        .artifact
        .unwrap();
    assert_eq!(first.run_i64().unwrap(), 48);
    let cached_parent = compiler.interface_cache_stats();

    let child = compiler
        .import_revision(
            world("semantic-core@0.2.0", provider("infixr")),
            Some(parent),
        )
        .unwrap();
    let second = compiler
        .compile_revision(child)
        .expect("a versioned provider update must re-elaborate the facade artifact")
        .artifact
        .unwrap();
    assert_eq!(second.run_i64().unwrap(), 52);
    assert_ne!(first.fingerprint(), second.fingerprint());
    assert_ne!(first.canonical_bytes(), second.canonical_bytes());
    assert!(
        compiler.interface_cache_stats().misses > cached_parent.misses,
        "the new provider version and dependent facade cannot reuse stale frozen interfaces"
    );

    let facade = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-facade@0.1.0".into()),
        path: "crate".into(),
    });
    let first_facade = compiler
        .dependency_trace(parent, &facade)
        .expect("parent facade interface must be published");
    let second_facade = compiler
        .dependency_trace(child, &facade)
        .expect("child facade interface must be published");
    assert_ne!(first_facade.fingerprint, second_facade.fingerprint);
    assert!(matches!(second_facade.status, DependencyStatus::Red { .. }));
    let parent_artifact = compiler
        .dependency_traces(parent)
        .into_iter()
        .find(|trace| {
            matches!(
                &trace.node,
                DependencyNode::Artifact(package) if package == &PackageKey("app@0.1.0".into())
            )
        })
        .expect("the parent must publish its linked artifact trace");
    let child_artifact = compiler
        .dependency_traces(child)
        .into_iter()
        .find(|trace| {
            matches!(
                &trace.node,
                DependencyNode::Artifact(package) if package == &PackageKey("app@0.1.0".into())
            )
        })
        .expect("the child must publish a freshly linked artifact trace");
    assert_ne!(
        parent_artifact.fingerprint, child_artifact.fingerprint,
        "the linked root product must not retain stale canonical metadata"
    );
}

#[test]
fn service_recovers_from_hyphen_alias_version_collisions_without_stale_generic_facade_state() {
    let root = "use semantic_facade::*; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn call(callback: Callback<i64>) -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: call(Capability<i64>::relay) }; Trace<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let provider = |fixity: &str| {
        format!(
            "pub {fixity} 30 **; pub trait Combine<T> {{ **(left: T, right: T) -> T; }} impl Combine<i64> for i64 {{ **(left: i64, right: i64) -> i64 {{ left - right }} }} pub effect Trace<T> {{ [1,1] note(value: T) -> i64; }} pub trait Parent<T> {{ type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / {{ <Self as Parent<T>>::Effects<U> }}; }} pub trait Child<T>: Parent<T> {{}} impl Parent<i64> for i64 {{ type Item<U> = i64; type Effects<U> = {{Trace<U>}}; fn relay<U>(receiver: i64, value: U) -> i64 / {{Trace<U>}} {{ Trace<U>::note(value) }} }} impl Child<i64> for i64 {{}} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / {{ <i64 as Child<i64>>::Effects<U> }};"
        )
    };
    let facade = "pub use semantic_lib::{Callback, Child as Capability, Trace}; pub use semantic_lib::*;";
    let world = |providers: Vec<(&str, String)>| {
        let mut input = request(root);
        for (package, source) in providers {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                source.as_bytes(),
            ));
        }
        input.sources.push(SourceInput::new(
            PackageKey("semantic-facade@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            facade.as_bytes(),
        ));
        input
    };

    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            world(vec![("semantic-lib@0.1.0", provider("infixl"))]),
            None,
        )
        .unwrap();
    let first = compiler
        .compile_revision(parent)
        .expect("the initial hyphenated generic facade must compile")
        .artifact
        .unwrap();
    assert_eq!(first.run_i64().unwrap(), 48);
    let cached_parent = compiler.interface_cache_stats();
    let facade_node = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-facade@0.1.0".into()),
        path: "crate".into(),
    });
    let published_facade = compiler
        .dependency_trace(parent, &facade_node)
        .expect("parent facade interface must be published");

    let collision = world(vec![
        ("semantic-lib@0.1.0", provider("infixl")),
        ("semantic-lib@0.2.0", provider("infixr")),
    ]);
    let mut reversed_collision = collision.clone();
    reversed_collision.sources.reverse();
    let mut diagnostics_by_order = Vec::new();
    for input in [collision, reversed_collision] {
        let error = compiler
            .import_revision(input, Some(parent))
            .expect_err("colliding hyphenated package aliases unexpectedly admitted a revision");
        let diagnostics = error.diagnostics().to_vec();
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic.code == "G7036"),
            "missing package alias collision diagnostic: {diagnostics:#?}"
        );
        assert!(
            diagnostics.iter().all(|diagnostic| diagnostic.code == "G7036"),
            "alias collisions must fail before interface/body diagnostics: {diagnostics:#?}"
        );
        assert_eq!(
            compiler.interface_cache_stats(),
            cached_parent,
            "rejected aliases must not mutate the established interface cache"
        );
        assert_eq!(
            compiler.dependency_trace(parent, &facade_node),
            Some(published_facade.clone()),
            "rejected aliases must not overwrite an already-published generic facade"
        );
        diagnostics_by_order.push(diagnostics);
    }
    assert_eq!(
        diagnostics_by_order[0], diagnostics_by_order[1],
        "hyphenated version-alias rejection must be deterministic under source reordering"
    );

    let child = compiler
        .import_revision(
            world(vec![("semantic-lib@0.2.0", provider("infixr"))]),
            Some(parent),
        )
        .expect("a valid version update must remain admissible after alias rejection");
    let second = compiler
        .compile_revision(child)
        .expect("the recovered generic facade must not reuse stale fixity metadata")
        .artifact
        .unwrap();
    assert_eq!(second.run_i64().unwrap(), 52);
    assert_ne!(first.fingerprint(), second.fingerprint());
    assert_ne!(first.canonical_bytes(), second.canonical_bytes());
    let updated_facade = compiler
        .dependency_trace(child, &facade_node)
        .expect("recovered child facade interface must publish");
    assert_ne!(published_facade.fingerprint, updated_facade.fingerprint);
    assert!(matches!(updated_facade.status, DependencyStatus::Red { .. }));
}

#[test]
fn service_pins_same_alias_generic_dependency_worlds_without_interface_or_diagnostic_leaks() {
    let root = "use semantic_lib::*; pub struct Packet { value: <i64 as Child<i64>>::Item<i64> } pub fn call(callback: Callback<i64>) -> i64 / { <i64 as Child<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: call(Child<i64>::relay) }; Trace<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let compatible = "pub infixl 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let incompatible = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = Bool; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> Bool / {Trace<U>} { true } } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let world = |provider: &str| request_with_dependency(root, "semantic-lib@0.1.0", provider);

    let compiler = StageZeroCompiler::new();
    let parent = compiler.import_revision(world(compatible), None).unwrap();
    assert_eq!(
        compiler
            .compile_revision(parent)
            .expect("the first generic dependency world must compile")
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        48
    );
    let parent_session = compiler.open_session(parent).unwrap();
    let cached_parent = compiler.interface_cache_stats();
    let dependency_interface = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-lib@0.1.0".into()),
        path: "crate".into(),
    });
    let published_parent_interface = compiler
        .dependency_trace(parent, &dependency_interface)
        .expect("the first dependency interface must be published");

    let child_input = world(incompatible);
    let child = compiler
        .import_revision(child_input.clone(), Some(parent))
        .unwrap();
    let child_session = compiler.open_session(child).unwrap();
    let Err(grandiose_stage0::ServiceError::Failed(first_diagnostics)) =
        compiler.compile_session(&child_session)
    else {
        panic!("the incompatible same-alias generic dependency unexpectedly compiled");
    };
    assert!(
        first_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4107"),
        "the child must use its own incompatible generic public contract: {first_diagnostics:#?}"
    );
    assert_eq!(
        compiler.interface_cache_stats(),
        cached_parent,
        "a rejected child world must not publish cache evidence into the pinned parent"
    );
    assert!(
        compiler.dependency_traces(child).is_empty(),
        "a rejected child world must publish neither its dependency interface nor artifact"
    );
    assert_eq!(
        compiler.dependency_trace(parent, &dependency_interface),
        Some(published_parent_interface),
        "the child cannot overwrite the parent dependency interface with its same-alias contract"
    );
    assert_eq!(
        compiler
            .compile_session(&parent_session)
            .expect("the pinned parent session must not see child generic contracts")
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        48
    );

    let mut reordered_child = child_input;
    reordered_child.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(second_diagnostics)) =
        StageZeroCompiler::new().compile(reordered_child)
    else {
        panic!("source reordering changed the incompatible generic child into success");
    };
    assert_eq!(
        first_diagnostics, second_diagnostics,
        "same-alias generic diagnostics must be canonical across request worlds and source order"
    );
}

#[test]
fn service_isolates_private_authority_and_public_fixity_diagnostics_across_generic_dependency_worlds() {
    let root = "use semantic_lib::*; pub struct Packet { value: <i64 as Child<i64>>::Item<i64> } pub fn call(callback: Callback<i64>) -> i64 / { <i64 as Child<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: call(Child<i64>::relay) }; Trace<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let public_provider = |fixity: &str| {
        format!(
            "pub {fixity} 30 **; pub trait Combine<T> {{ **(left: T, right: T) -> T; }} impl Combine<i64> for i64 {{ **(left: i64, right: i64) -> i64 {{ left - right }} }} pub effect Trace<T> {{ [1,1] note(value: T) -> i64; }} pub trait Parent<T> {{ type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / {{ <Self as Parent<T>>::Effects<U> }}; }} pub trait Child<T>: Parent<T> {{}} impl Parent<i64> for i64 {{ type Item<U> = i64; type Effects<U> = {{Trace<U>}}; fn relay<U>(receiver: i64, value: U) -> i64 / {{Trace<U>}} {{ Trace<U>::note(value) }} }} impl Child<i64> for i64 {{}} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / {{ <i64 as Child<i64>>::Effects<U> }};"
        )
    };
    let private_provider = "pub infixl 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let world = |root: &str, provider: &str| {
        request_with_dependency(root, "semantic-lib@0.1.0", provider)
    };

    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(world(root, &public_provider("infixl")), None)
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(parent)
            .expect("the public generic parent world must compile")
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        48
    );
    let cached_parent = compiler.interface_cache_stats();
    let provider_interface = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-lib@0.1.0".into()),
        path: "crate".into(),
    });
    let published_parent = compiler
        .dependency_trace(parent, &provider_interface)
        .expect("the public parent interface must publish");

    let private_world = world(root, private_provider);
    let private_child = compiler
        .import_revision(private_world.clone(), Some(parent))
        .unwrap();
    let private_session = compiler.open_session(private_child).unwrap();
    let Err(grandiose_stage0::ServiceError::Failed(private_diagnostics)) =
        compiler.compile_session(&private_session)
    else {
        panic!("private generic authority unexpectedly inherited the public parent interface");
    };
    assert!(
        private_diagnostics
            .iter()
            .any(|diagnostic| matches!(diagnostic.code, "G3304" | "G3310" | "G3315")),
        "private child must report its own private generic declarations: {private_diagnostics:#?}"
    );
    assert!(
        private_diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "G4111"),
        "private child must not inherit public-fixity ambiguity: {private_diagnostics:#?}"
    );
    assert_eq!(compiler.interface_cache_stats(), cached_parent);
    assert!(compiler.dependency_traces(private_child).is_empty());
    assert_eq!(
        compiler.dependency_trace(parent, &provider_interface),
        Some(published_parent.clone())
    );
    let mut reordered_private = private_world;
    reordered_private.sources.reverse();
    assert_eq!(
        private_diagnostics,
        StageZeroCompiler::new()
            .compile(reordered_private)
            .expect_err("reordered private authority must still fail")
            .diagnostics()
            .to_vec()
    );

    let fixity_root = "use semantic_lib::*; use alternate_lib::*; pub fn main() -> i64 { 10 ** 3 ** 2 }";
    let mut fixity_world = world(fixity_root, &public_provider("infixl"));
    fixity_world.sources.push(SourceInput::new(
        PackageKey("alternate-lib@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        public_provider("infixr").as_bytes(),
    ));
    let fixity_child = compiler
        .import_revision(fixity_world.clone(), Some(parent))
        .unwrap();
    let fixity_session = compiler.open_session(fixity_child).unwrap();
    let Err(grandiose_stage0::ServiceError::Failed(fixity_diagnostics)) =
        compiler.compile_session(&fixity_session)
    else {
        panic!("two public same-spelled fixities unexpectedly inherited private authority failure");
    };
    assert!(
        fixity_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4111"),
        "public competing fixities must report their own grouping ambiguity: {fixity_diagnostics:#?}"
    );
    assert!(
        fixity_diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "G3317"),
        "public fixity world must not inherit private authority diagnostics: {fixity_diagnostics:#?}"
    );
    assert_eq!(compiler.interface_cache_stats(), cached_parent);
    assert!(compiler.dependency_traces(fixity_child).is_empty());
    let mut reordered_fixity = fixity_world;
    reordered_fixity.sources.reverse();
    assert_eq!(
        fixity_diagnostics,
        StageZeroCompiler::new()
            .compile(reordered_fixity)
            .expect_err("reordered public fixities must remain ambiguous")
            .diagnostics()
            .to_vec()
    );

    let repaired = compiler
        .import_revision(world(root, &public_provider("infixr")), Some(parent))
        .unwrap();
    let repaired_artifact = compiler
        .compile_revision(repaired)
        .expect("a repaired public world must not retain either rejected diagnostic set")
        .artifact
        .unwrap();
    assert_eq!(repaired_artifact.run_i64().unwrap(), 52);
    assert!(
        compiler.interface_cache_stats().misses > cached_parent.misses,
        "the repaired public generic interface must be collected after rejected worlds"
    );
}

#[test]
fn service_canonicalizes_mixed_invalid_versioned_provider_diagnostics_without_cache_leaks() {
    let valid_root = "use semantic_lib::*; pub struct Packet { value: <i64 as Child<i64>>::Item<i64> } pub fn call(callback: Callback<i64>) -> i64 / { <i64 as Child<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: call(Child<i64>::relay) }; Trace<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let mixed_root = "use semantic_lib::*; use alternate_lib::*; pub fn call(callback: Callback<i64>) -> i64 { callback(0, 41) } pub fn hidden() -> i64 / Trace<i64> { Trace<i64>::note(41) } pub fn main() -> i64 { 10 ** 3 ** 2 }";
    let valid_provider = |fixity: &str| {
        format!(
            "pub {fixity} 30 **; pub trait Combine<T> {{ **(left: T, right: T) -> T; }} impl Combine<i64> for i64 {{ **(left: i64, right: i64) -> i64 {{ left - right }} }} pub effect Trace<T> {{ [1,1] note(value: T) -> i64; }} pub trait Parent<T> {{ type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / {{ <Self as Parent<T>>::Effects<U> }}; }} pub trait Child<T>: Parent<T> {{}} impl Parent<i64> for i64 {{ type Item<U> = i64; type Effects<U> = {{Trace<U>}}; fn relay<U>(receiver: i64, value: U) -> i64 / {{Trace<U>}} {{ Trace<U>::note(value) }} }} impl Child<i64> for i64 {{}} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / {{ <i64 as Child<i64>>::Effects<U> }};"
        )
    };
    let mixed_provider = "pub infixl 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = Bool; } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U>;";
    let alternate = "pub infixr 30 **; pub trait Combine { **(left: i64, right: i64) -> i64; } impl Combine for i64 { **(left: i64, right: i64) -> i64 { left - right } }";
    let world = |root: &str, package: &str, provider: &str, include_alternate: bool| {
        let mut input = request_with_dependency(root, package, provider);
        if include_alternate {
            input.sources.push(SourceInput::new(
                PackageKey("alternate-lib@0.1.0".into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                alternate.as_bytes(),
            ));
        }
        input
    };

    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            world(valid_root, "semantic-lib@0.1.0", &valid_provider("infixl"), false),
            None,
        )
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(parent)
            .expect("the public provider parent must compile")
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        48
    );
    let cached_parent = compiler.interface_cache_stats();
    let parent_provider = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-lib@0.1.0".into()),
        path: "crate".into(),
    });
    let published_parent = compiler
        .dependency_trace(parent, &parent_provider)
        .expect("the parent provider interface must be published");

    let mixed_world = world(mixed_root, "semantic-lib@0.2.0", mixed_provider, true);
    let child = compiler
        .import_revision(mixed_world.clone(), Some(parent))
        .unwrap();
    let session = compiler.open_session(child).unwrap();
    let Err(grandiose_stage0::ServiceError::Failed(first_diagnostics)) =
        compiler.compile_session(&session)
    else {
        panic!("mixed private/GAT/fixity provider world unexpectedly compiled");
    };
    let codes = first_diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<Vec<_>>();
    assert_eq!(
        codes,
        vec!["G3315"],
        "private interface authority must stop the later GAT-call and fixity body errors: {first_diagnostics:#?}"
    );
    assert_eq!(
        compiler.interface_cache_stats(),
        cached_parent,
        "mixed failure must not publish cache state"
    );
    assert!(
        compiler.dependency_traces(child).is_empty(),
        "mixed failure must not publish interfaces or artifacts"
    );
    assert_eq!(
        compiler.dependency_trace(parent, &parent_provider),
        Some(published_parent),
        "mixed version diagnostics must not overwrite the parent provider interface"
    );
    let mut reordered_mixed = mixed_world;
    reordered_mixed.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(second_diagnostics)) =
        StageZeroCompiler::new().compile(reordered_mixed)
    else {
        panic!("source reordering changed mixed diagnostics into success");
    };
    assert_eq!(
        first_diagnostics, second_diagnostics,
        "mixed version diagnostics, including their canonical order, must be exact"
    );

    let repaired = compiler
        .import_revision(
            world(valid_root, "semantic-lib@0.2.0", &valid_provider("infixr"), false),
            Some(parent),
        )
        .unwrap();
    let artifact = compiler
        .compile_revision(repaired)
        .expect("a repaired provider version must not retain mixed diagnostics")
        .artifact
        .unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 52);
    assert!(compiler.interface_cache_stats().misses > cached_parent.misses);
}

#[test]
fn service_executes_cross_package_public_module_reexport_cycles_with_one_generic_provider_identity() {
    let root = "use cycle_facade::*; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn call(callback: Callback<i64>) -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: call(Capability<i64>::relay) }; Trace<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let mut input = request(root);
    for (package, path, source) in [
        ("semantic-core@0.1.0", "src/lib.glorious", provider),
        (
            "cycle-facade@0.1.0",
            "src/lib.glorious",
            "pub mod left; pub mod right; pub use crate::left::*; pub use crate::right::*;",
        ),
        (
            "cycle-facade@0.1.0",
            "src/left/left.glorious",
            "pub use crate::right::*; pub use semantic_core::{Callback, Child as Capability, Trace}; pub use semantic_core::*;",
        ),
        (
            "cycle-facade@0.1.0",
            "src/right/right.glorious",
            "pub use crate::left::*; pub use semantic_core::{Callback, Child as Capability, Trace}; pub use semantic_core::*;",
        ),
    ] {
        input.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse(path).unwrap(),
            source.as_bytes(),
        ));
    }
    let compiler = StageZeroCompiler::new();
    let parent = compiler.import_revision(input.clone(), None).unwrap();
    let first = compiler
        .compile_revision(parent)
        .expect("a module-level facade cycle must retain its one upstream provider identity");
    let stats = compiler.interface_cache_stats();
    let mut reordered = input;
    reordered.sources.reverse();
    let child = compiler.import_revision(reordered, Some(parent)).unwrap();
    assert_eq!(child, parent, "canonical source worlds must deduplicate module-cycle input order");
    let second = compiler
        .compile_revision(child)
        .expect("reordered module-cycle sources must preserve the legal interface cycle");
    assert_eq!(compiler.interface_cache_stats().misses, stats.misses);
    assert_eq!(compiler.interface_cache_stats().hits, stats.hits + 5);
    let provider_interface = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-core@0.1.0".into()),
        path: "crate".into(),
    });
    for path in ["crate", "crate::left", "crate::right"] {
        let facade_interface = DependencyNode::Interface(ModuleKey {
            package: PackageKey("cycle-facade@0.1.0".into()),
            path: path.into(),
        });
        let trace = compiler
            .dependency_trace(parent, &facade_interface)
            .expect("each public cycle member must publish one frozen interface");
        assert!(
            trace.dependencies.contains(&provider_interface),
            "{path} must retain the semantic provider identity it re-exports"
        );
    }
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 52);
    assert_eq!(second.run_i64().unwrap(), 52);
}

#[test]
fn service_rejects_private_provider_authority_through_cross_package_module_reexport_cycles() {
    let provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let mut input = request("use cycle_facade::*; pub fn main() -> i64 { 10 ** 3 ** 2 }");
    for (package, path, source) in [
        ("semantic-core@0.1.0", "src/lib.glorious", provider),
        (
            "cycle-facade@0.1.0",
            "src/lib.glorious",
            "pub mod left; pub mod right; pub use crate::left::*; pub use crate::right::*;",
        ),
        (
            "cycle-facade@0.1.0",
            "src/left/left.glorious",
            "pub use crate::right::*; pub use semantic_core::{Callback, Child as Capability, Trace}; pub use semantic_core::*;",
        ),
        (
            "cycle-facade@0.1.0",
            "src/right/right.glorious",
            "pub use crate::left::*; pub use semantic_core::{Callback, Child as Capability, Trace}; pub use semantic_core::*;",
        ),
    ] {
        input.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse(path).unwrap(),
            source.as_bytes(),
        ));
    }
    let mut reordered = input.clone();
    reordered.sources.reverse();
    let mut diagnostics_by_order = Vec::new();
    for request in [input, reordered] {
        let compiler = StageZeroCompiler::new();
        let revision = compiler.import_revision(request, None).unwrap();
        let session = compiler.open_session(revision).unwrap();
        let error = compiler
            .compile_session(&session)
            .expect_err("private provider contracts cannot pass a public module-cycle facade");
        assert!(
            error.diagnostics().iter().all(|diagnostic| diagnostic.code == "G3317"),
            "private facade cycle must fail before body grouping: {:#?}",
            error.diagnostics()
        );
        assert_eq!(compiler.interface_cache_stats().hits, 0);
        assert_eq!(compiler.interface_cache_stats().misses, 0);
        assert!(compiler.dependency_traces(revision).is_empty());
        diagnostics_by_order.push(error.diagnostics().to_vec());
    }
    assert_eq!(diagnostics_by_order[0], diagnostics_by_order[1]);
}

#[test]
fn service_rolls_back_private_alias_exports_through_public_package_module_cycles() {
    let root = "use cycle_facade::*; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn call(callback: Relay<i64>) -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Audit<i64> { let packet = Packet { value: call(Capability<i64>::relay) }; Audit<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Audit<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let public_provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let private_provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let world = |provider: &str| {
        let mut input = request(root);
        for (package, path, source) in [
            ("semantic-core@0.1.0", "src/lib.glorious", provider),
            (
                "cycle-facade@0.1.0",
                "src/lib.glorious",
                "pub mod api; pub mod bridge; pub use crate::api::*; pub use crate::bridge::*;",
            ),
            (
                "cycle-facade@0.1.0",
                "src/api/api.glorious",
                "pub use crate::bridge::*; pub use semantic_core::{Child as Capability, Trace as Audit};",
            ),
            (
                "cycle-facade@0.1.0",
                "src/bridge/bridge.glorious",
                "pub use crate::api::*; pub use semantic_core::{Callback as Relay, Combine as Operator}; pub use semantic_core::*;",
            ),
        ] {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse(path).unwrap(),
                source.as_bytes(),
            ));
        }
        input
    };

    let compiler = StageZeroCompiler::new();
    let public = world(public_provider);
    let parent = compiler.import_revision(public, None).unwrap();
    let artifact = compiler
        .compile_revision(parent)
        .expect("public cyclic aliases must retain generic traits, effects, and fixity authority")
        .artifact
        .unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 52);
    let provider_interface = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-core@0.1.0".into()),
        path: "crate".into(),
    });
    let mut published = Vec::new();
    for path in ["crate", "crate::api", "crate::bridge"] {
        let interface = DependencyNode::Interface(ModuleKey {
            package: PackageKey("cycle-facade@0.1.0".into()),
            path: path.into(),
        });
        let trace = compiler
            .dependency_trace(parent, &interface)
            .expect("every public module-cycle member must publish one sealed interface");
        assert!(
            trace.dependencies.contains(&provider_interface),
            "{path} must retain the generic provider identity behind its aliases"
        );
        published.push((interface, trace));
    }
    let cached = compiler.interface_cache_stats();

    let private = world(private_provider);
    let child = compiler.import_revision(private.clone(), Some(parent)).unwrap();
    let error = compiler
        .compile_session(&compiler.open_session(child).unwrap())
        .expect_err("private trait/effect aliases cannot cross a public module cycle");
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "cyclic facade authority must reject a private alias export: {:#?}",
        error.diagnostics()
    );
    assert!(
        error
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code != "G4111"),
        "private cyclic aliases must not become a public operator ambiguity: {:#?}",
        error.diagnostics()
    );
    assert_eq!(
        compiler.interface_cache_stats(),
        cached,
        "a private cyclic alias branch must not publish or perturb cache products"
    );
    assert!(
        compiler.dependency_traces(child).is_empty(),
        "a failed cyclic alias world must roll back every staged interface trace"
    );
    for (interface, trace) in published {
        assert_eq!(
            compiler.dependency_trace(parent, &interface),
            Some(trace),
            "the failed child must not overwrite a public parent interface"
        );
    }

    let mut reordered_private = private;
    reordered_private.sources.reverse();
    let second = StageZeroCompiler::new()
        .compile(reordered_private)
        .expect_err("source order cannot authorize private cyclic aliases");
    assert_eq!(
        error.diagnostics(),
        second.diagnostics(),
        "private cyclic alias diagnostics must be canonical under source reordering"
    );
}

#[test]
fn service_recovers_versioned_public_cycle_aliases_after_private_incompatible_revision() {
    let root = "use cycle_facade::*; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn call(callback: Relay<i64>) -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Audit<i64> { let packet = Packet { value: call(Capability<i64>::relay) }; Audit<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Audit<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let public_provider = |fixity: &str| {
        format!(
            "pub {fixity} 30 **; pub trait Combine<T> {{ **(left: T, right: T) -> T; }} impl Combine<i64> for i64 {{ **(left: i64, right: i64) -> i64 {{ left - right }} }} pub effect Trace<T> {{ [1,1] note(value: T) -> i64; }} pub trait Parent<T> {{ type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / {{ <Self as Parent<T>>::Effects<U> }}; }} pub trait Child<T>: Parent<T> {{}} impl Parent<i64> for i64 {{ type Item<U> = i64; type Effects<U> = {{Trace<U>}}; fn relay<U>(receiver: i64, value: U) -> i64 / {{Trace<U>}} {{ Trace<U>::note(value) }} }} impl Child<i64> for i64 {{}} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / {{ <i64 as Child<i64>>::Effects<U> }};"
        )
    };
    let private_incompatible = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = Bool; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> Bool / {Trace<U>} { true } } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let world = |package: &str, provider: String| {
        let mut input = request(root);
        for (package, path, source) in [
            (package, "src/lib.glorious", provider),
            (
                "cycle-facade@0.1.0",
                "src/lib.glorious",
                "pub mod api; pub mod bridge; pub use crate::api::*; pub use crate::bridge::*;".into(),
            ),
            (
                "cycle-facade@0.1.0",
                "src/api/api.glorious",
                "pub use crate::bridge::*; pub use semantic_core::{Child as Capability, Trace as Audit};".into(),
            ),
            (
                "cycle-facade@0.1.0",
                "src/bridge/bridge.glorious",
                "pub use crate::api::*; pub use semantic_core::{Callback as Relay, Combine as Operator}; pub use semantic_core::*;".into(),
            ),
        ] {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse(path).unwrap(),
                source.into_bytes(),
            ));
        }
        input
    };

    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(world("semantic-core@0.1.0", public_provider("infixl")), None)
        .unwrap();
    let first = compiler
        .compile_revision(parent)
        .expect("the initial public cyclic alias world must compile")
        .artifact
        .unwrap();
    assert_eq!(first.run_i64().unwrap(), 48);
    let cached_parent = compiler.interface_cache_stats();
    let facade_node = DependencyNode::Interface(ModuleKey {
        package: PackageKey("cycle-facade@0.1.0".into()),
        path: "crate".into(),
    });
    let published_parent = compiler
        .dependency_trace(parent, &facade_node)
        .expect("the initial cyclic facade interface must publish");

    let rejected_world = world("semantic-core@0.2.0", private_incompatible.into());
    let rejected = compiler
        .import_revision(rejected_world.clone(), Some(parent))
        .unwrap();
    let error = compiler
        .compile_session(&compiler.open_session(rejected).unwrap())
        .expect_err("a private incompatible provider revision cannot cross cyclic aliases");
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "private provider aliases must fail in their own revision: {:#?}",
        error.diagnostics()
    );
    assert!(
        error
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code != "G4111"),
        "the rejected revision must not leak an operator ambiguity: {:#?}",
        error.diagnostics()
    );
    assert_eq!(compiler.interface_cache_stats(), cached_parent);
    assert!(compiler.dependency_traces(rejected).is_empty());
    assert_eq!(
        compiler.dependency_trace(parent, &facade_node),
        Some(published_parent.clone()),
        "the rejected revision must not overwrite its public cyclic facade parent"
    );
    let mut reordered_rejected = rejected_world;
    reordered_rejected.sources.reverse();
    assert_eq!(
        error.diagnostics(),
        StageZeroCompiler::new()
            .compile(reordered_rejected)
            .expect_err("source reordering cannot authorize the private cyclic revision")
            .diagnostics(),
        "private incompatible cyclic diagnostics must be canonical"
    );

    let repaired = compiler
        .import_revision(
            world("semantic-core@0.2.0", public_provider("infixr")),
            Some(parent),
        )
        .unwrap();
    let second = compiler
        .compile_revision(repaired)
        .expect("a repaired public provider revision must not retain private diagnostics")
        .artifact
        .unwrap();
    assert_eq!(second.run_i64().unwrap(), 52);
    assert_ne!(first.fingerprint(), second.fingerprint());
    assert_ne!(first.canonical_bytes(), second.canonical_bytes());
    let repaired_facade = compiler
        .dependency_trace(repaired, &facade_node)
        .expect("the repaired cyclic facade must publish a new interface");
    assert_ne!(published_parent.fingerprint, repaired_facade.fingerprint);
    assert!(
        compiler.interface_cache_stats().misses > cached_parent.misses,
        "the repaired provider revision must collect fresh cyclic facade interfaces"
    );
}

#[test]
fn service_isolates_parallel_cyclic_facades_across_versioned_provider_worlds() {
    let root = "use left_facade::*; use right_facade::{Child as RightCapability, Trace as RightTrace}; pub struct LeftPacket { value: <i64 as Child<i64>>::Item<i64> } pub struct RightPacket { value: <i64 as RightCapability<i64>>::Item<i64> } pub fn left_worker() -> i64 / Trace<i64> { let packet = LeftPacket { value: Child<i64>::relay(0, 41) }; Trace<i64>::note(packet.value) } pub fn right_worker() -> i64 / RightTrace<i64> { let packet = RightPacket { value: RightCapability<i64>::relay(0, 41) }; RightTrace<i64>::note(packet.value) } pub fn left_value() -> i64 { handle left_worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn right_value() -> i64 { handle right_worker() { RightTrace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + left_value() + right_value() }";
    let public_provider = |fixity: &str| {
        format!(
            "pub {fixity} 30 **; pub trait Combine<T> {{ **(left: T, right: T) -> T; }} impl Combine<i64> for i64 {{ **(left: i64, right: i64) -> i64 {{ left - right }} }} pub effect Trace<T> {{ [1,1] note(value: T) -> i64; }} pub trait Parent<T> {{ type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / {{ <Self as Parent<T>>::Effects<U> }}; }} pub trait Child<T>: Parent<T> {{}} impl Parent<i64> for i64 {{ type Item<U> = i64; type Effects<U> = {{Trace<U>}}; fn relay<U>(receiver: i64, value: U) -> i64 / {{Trace<U>}} {{ Trace<U>::note(value) }} }} impl Child<i64> for i64 {{}} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / {{ <i64 as Child<i64>>::Effects<U> }};"
        )
    };
    let private_incompatible = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = Bool; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> Bool / {Trace<U>} { true } } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let world = |provider_package: &str, provider: String| {
        let mut input = request(root);
        input.sources.push(SourceInput::new(
            PackageKey(provider_package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            provider.into_bytes(),
        ));
        for package in ["left-facade@0.1.0", "right-facade@0.1.0"] {
            for (path, source) in [
                (
                    "src/lib.glorious",
                    "pub mod api; pub mod bridge; pub use crate::api::*; pub use crate::bridge::*;",
                ),
                (
                    "src/api/api.glorious",
                    "pub use crate::bridge::*; pub use semantic_core::{Child, Trace};",
                ),
                (
                    "src/bridge/bridge.glorious",
                    "pub use crate::api::*; pub use semantic_core::*;",
                ),
            ] {
                input.sources.push(SourceInput::new(
                    PackageKey(package.into()),
                    LogicalPath::parse(path).unwrap(),
                    source.as_bytes(),
                ));
            }
        }
        input
    };

    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(world("semantic-core@0.1.0", public_provider("infixl")), None)
        .unwrap();
    let first = compiler
        .compile_revision(parent)
        .expect("parallel cyclic facades must share their initial provider world")
        .artifact
        .unwrap();
    assert_eq!(first.run_i64().unwrap(), 91);
    let cached_parent = compiler.interface_cache_stats();
    let parent_provider = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-core@0.1.0".into()),
        path: "crate".into(),
    });
    let mut published = Vec::new();
    for package in ["left-facade@0.1.0", "right-facade@0.1.0"] {
        for path in ["crate", "crate::api", "crate::bridge"] {
            let node = DependencyNode::Interface(ModuleKey {
                package: PackageKey(package.into()),
                path: path.into(),
            });
            let trace = compiler
                .dependency_trace(parent, &node)
                .expect("every initial cyclic facade interface must freeze");
            assert!(
                trace.dependencies.contains(&parent_provider),
                "{package}::{path} must retain the initial provider identity"
            );
            published.push((node, trace));
        }
    }

    let rejected_world = world("semantic-core@0.2.0", private_incompatible.into());
    let rejected = compiler
        .import_revision(rejected_world.clone(), Some(parent))
        .unwrap();
    let error = compiler
        .compile_session(&compiler.open_session(rejected).unwrap())
        .expect_err("private incompatible provider state cannot cross either facade cycle");
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| matches!(diagnostic.code, "G3317" | "G3326")),
        "the rejected world must identify its own inaccessible cyclic aliases: {:#?}",
        error.diagnostics()
    );
    assert!(
        error
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code != "G4111"),
        "the rejected provider revision must not inherit a public fixity ambiguity: {:#?}",
        error.diagnostics()
    );
    assert_eq!(compiler.interface_cache_stats(), cached_parent);
    assert!(compiler.dependency_traces(rejected).is_empty());
    for (node, trace) in &published {
        assert_eq!(
            compiler.dependency_trace(parent, node),
            Some(trace.clone()),
            "the rejected world must not overwrite an initial cyclic facade interface"
        );
    }
    let mut reordered_rejected = rejected_world;
    reordered_rejected.sources.reverse();
    assert_eq!(
        error.diagnostics(),
        StageZeroCompiler::new()
            .compile(reordered_rejected)
            .expect_err("source reordering cannot admit the rejected parallel world")
            .diagnostics(),
        "rejected parallel cyclic diagnostics must be canonical"
    );

    let repaired = compiler
        .import_revision(
            world("semantic-core@0.2.0", public_provider("infixr")),
            Some(parent),
        )
        .unwrap();
    let second = compiler
        .compile_revision(repaired)
        .expect("the repaired provider revision must compile through both cyclic facades")
        .artifact
        .unwrap();
    assert_eq!(second.run_i64().unwrap(), 95);
    assert_ne!(first.fingerprint(), second.fingerprint());
    assert_ne!(first.canonical_bytes(), second.canonical_bytes());
    let repaired_provider = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-core@0.2.0".into()),
        path: "crate".into(),
    });
    for (node, parent_trace) in published {
        let repaired_trace = compiler
            .dependency_trace(repaired, &node)
            .expect("every repaired cyclic facade interface must freeze anew");
        assert!(repaired_trace.dependencies.contains(&repaired_provider));
        assert_ne!(parent_trace.fingerprint, repaired_trace.fingerprint);
    }
    assert!(
        compiler.interface_cache_stats().misses > cached_parent.misses,
        "the repaired parallel world must collect fresh package interfaces"
    );
}

#[test]
fn service_recovers_three_version_cyclic_alias_slice_without_stale_publication() {
    let executable_root = "use cycle_facade::*; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn call(callback: Relay<i64>) -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Audit<i64> { let packet = Packet { value: call(Capability<i64>::relay) }; Audit<i64>::note(packet.value) } pub fn effect_value() -> i64 { handle worker() { Audit<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + effect_value() }";
    let authority_root = "pub fn main() -> i64 { 0 }";
    let public_provider = |fixity: &str| {
        format!(
            "pub {fixity} 30 **; pub trait Combine<T> {{ **(left: T, right: T) -> T; }} impl Combine<i64> for i64 {{ **(left: i64, right: i64) -> i64 {{ left - right }} }} pub effect Trace<T> {{ [1,1] note(value: T) -> i64; }} pub trait Parent<T> {{ type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / {{ <Self as Parent<T>>::Effects<U> }}; }} pub trait Child<T>: Parent<T> {{}} impl Parent<i64> for i64 {{ type Item<U> = i64; type Effects<U> = {{Trace<U>}}; fn relay<U>(receiver: i64, value: U) -> i64 / {{Trace<U>}} {{ Trace<U>::note(value) }} }} impl Child<i64> for i64 {{}} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / {{ <i64 as Child<i64>>::Effects<U> }};"
        )
    };
    let private_provider = "pub infixl 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = Bool; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> Bool / {Trace<U>} { true } } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let world = |root: &str,
                 providers: Vec<(&str, String)>,
                 api_provider: &str,
                 bridge_provider: &str| {
        let mut input = request(root);
        for (package, source) in providers {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                source.into_bytes(),
            ));
        }
        for (path, source) in [
            (
                "src/lib.glorious",
                "pub mod api; pub mod bridge; pub use crate::api::*; pub use crate::bridge::*;"
                    .to_owned(),
            ),
            (
                "src/api/api.glorious",
                format!(
                    "pub use crate::bridge::*; pub use {api_provider}::{{Callback as Relay, Child as Capability, Combine as Operator, Trace as Audit}}; pub use {api_provider}::*;"
                ),
            ),
            (
                "src/bridge/bridge.glorious",
                format!(
                    "pub use crate::api::*; pub use {bridge_provider}::{{Callback as Relay, Child as Capability, Combine as Operator, Trace as Audit}}; pub use {bridge_provider}::*;"
                ),
            ),
        ] {
            input.sources.push(SourceInput::new(
                PackageKey("cycle-facade@0.1.0".into()),
                LogicalPath::parse(path).unwrap(),
                source.into_bytes(),
            ));
        }
        input
    };

    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            world(
                executable_root,
                vec![("semantic-core@0.1.0", public_provider("infixl"))],
                "semantic_core",
                "semantic_core",
            ),
            None,
        )
        .unwrap();
    let first = compiler
        .compile_revision(parent)
        .expect("v0.1 must seal one public provider through the cyclic facade")
        .artifact
        .unwrap();
    assert_eq!(first.run_i64().unwrap(), 48);
    let cached_parent = compiler.interface_cache_stats();
    let parent_provider = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-core@0.1.0".into()),
        path: "crate".into(),
    });
    let mut parent_interfaces = Vec::new();
    for path in ["crate", "crate::api", "crate::bridge"] {
        let node = DependencyNode::Interface(ModuleKey {
            package: PackageKey("cycle-facade@0.1.0".into()),
            path: path.into(),
        });
        let trace = compiler
            .dependency_trace(parent, &node)
            .expect("each v0.1 cyclic facade interface must publish");
        assert!(trace.dependencies.contains(&parent_provider));
        parent_interfaces.push((node, trace));
    }

    let rejected_world = world(
        authority_root,
        vec![
            ("alpha-core@0.2.0", private_provider.into()),
            ("beta-core@0.2.0", public_provider("infixr")),
        ],
        "alpha_core",
        "beta_core",
    );
    let rejected = compiler
        .import_revision(rejected_world.clone(), Some(parent))
        .unwrap();
    let error = compiler
        .compile_session(&compiler.open_session(rejected).unwrap())
        .expect_err("v0.2 cannot merge private and distinct public generic aliases");
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| matches!(diagnostic.code, "G3317" | "G3318")),
        "v0.2 must identify private authority or provider identity at the interface: {:#?}",
        error.diagnostics()
    );
    assert!(
        error.diagnostics().iter().all(|diagnostic| {
            matches!(diagnostic.code, "G3317" | "G3318" | "G4111")
        }),
        "v0.2 must stop at authority/identity/fixity ambiguity before body publication: {:#?}",
        error.diagnostics()
    );
    assert_eq!(compiler.interface_cache_stats(), cached_parent);
    assert!(compiler.dependency_traces(rejected).is_empty());
    for (node, trace) in &parent_interfaces {
        assert_eq!(compiler.dependency_trace(parent, node), Some(trace.clone()));
    }
    let mut reordered_rejected = rejected_world;
    reordered_rejected.sources.reverse();
    assert_eq!(
        error.diagnostics(),
        StageZeroCompiler::new()
            .compile(reordered_rejected)
            .expect_err("v0.2 source ordering cannot bypass interface authority")
            .diagnostics(),
        "v0.2 authority/identity diagnostics must be canonical"
    );

    let repaired = compiler
        .import_revision(
            world(
                executable_root,
                vec![("semantic-core@0.3.0", public_provider("infixr"))],
                "semantic_core",
                "semantic_core",
            ),
            Some(parent),
        )
        .unwrap();
    let third = compiler
        .compile_revision(repaired)
        .expect("v0.3 must repair the cyclic public surface without v0.2 diagnostics")
        .artifact
        .unwrap();
    assert_eq!(third.run_i64().unwrap(), 52);
    assert_ne!(first.fingerprint(), third.fingerprint());
    assert_ne!(first.canonical_bytes(), third.canonical_bytes());
    let repaired_provider = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-core@0.3.0".into()),
        path: "crate".into(),
    });
    for (node, parent_trace) in parent_interfaces {
        let repaired_trace = compiler
            .dependency_trace(repaired, &node)
            .expect("each repaired cyclic interface must freeze in v0.3");
        assert!(repaired_trace.dependencies.contains(&repaired_provider));
        assert_ne!(parent_trace.fingerprint, repaired_trace.fingerprint);
    }
    assert!(
        compiler.interface_cache_stats().misses > cached_parent.misses,
        "v0.3 must collect fresh provider and facade cache products"
    );
}

#[test]
fn service_isolates_unrelated_generic_diamonds_from_private_callable_revisions() {
    let root = "use left_diamond::*; use right_diamond::{Callback as RightRelay, Child as RightCapability, Trace as RightTrace}; pub struct LeftPacket { value: <i64 as Child<i64>>::Item<i64> } pub struct RightPacket { value: <i64 as RightCapability<i64>>::Item<i64> } pub fn left_call(callback: Callback<i64>) -> i64 / { <i64 as Child<i64>>::Effects<i64> } { callback(0, 41) } pub fn left_worker() -> i64 / Trace<i64> { let packet = LeftPacket { value: left_call(Child<i64>::relay) }; Trace<i64>::note(packet.value) } pub fn right_call(callback: RightRelay<i64>) -> i64 / { <i64 as RightCapability<i64>>::Effects<i64> } { callback(0, 41) } pub fn right_worker() -> i64 / RightTrace<i64> { let packet = RightPacket { value: right_call(RightCapability<i64>::relay) }; RightTrace<i64>::note(packet.value) } pub fn left_value() -> i64 { handle left_worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn right_value() -> i64 { handle right_worker() { RightTrace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + left_value() + right_value() }";
    let right_root = "use right_diamond::*; pub struct Packet { value: <i64 as Child<i64>>::Item<i64> } pub fn call(callback: Callback<i64>) -> i64 / { <i64 as Child<i64>>::Effects<i64> } { callback(0, 41) } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: call(Child<i64>::relay) }; Trace<i64>::note(packet.value) } pub fn main() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } }";
    let public_provider = |fixity: &str| {
        format!(
            "pub {fixity} 30 **; pub trait Combine<T> {{ **(left: T, right: T) -> T; }} impl Combine<i64> for i64 {{ **(left: i64, right: i64) -> i64 {{ left - right }} }} pub effect Trace<T> {{ [1,1] note(value: T) -> i64; }} pub trait Parent<T> {{ type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / {{ <Self as Parent<T>>::Effects<U> }}; }} pub trait Child<T>: Parent<T> {{}} impl Parent<i64> for i64 {{ type Item<U> = i64; type Effects<U> = {{Trace<U>}}; fn relay<U>(receiver: i64, value: U) -> i64 / {{Trace<U>}} {{ Trace<U>::note(value) }} }} impl Child<i64> for i64 {{}} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / {{ <i64 as Child<i64>>::Effects<U> }};"
        )
    };
    let private_provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = Bool; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> Bool / {Trace<U>} { true } } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let diamond_sources = |prefix: &str, provider_alias: &str| {
        let a_package = format!("{prefix}-a@0.1.0");
        let b_package = format!("{prefix}-b@0.1.0");
        let top_package = format!("{prefix}-diamond@0.1.0");
        vec![
            (a_package, format!("pub use {provider_alias}::*;")),
            (b_package, format!("pub use {provider_alias}::*;")),
            (
                top_package,
                format!("pub use {}::*; pub use {}::*;", prefix.replace('-', "_") + "_a", prefix.replace('-', "_") + "_b"),
            ),
        ]
    };
    let world = |root: &str, left_provider: (&str, String), include_left: bool| {
        let mut input = request(root);
        if include_left {
            input.sources.push(SourceInput::new(
                PackageKey(left_provider.0.into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                left_provider.1.into_bytes(),
            ));
            for (package, source) in diamond_sources("left", "left_core") {
                input.sources.push(SourceInput::new(
                    PackageKey(package),
                    LogicalPath::parse("src/lib.glorious").unwrap(),
                    source.into_bytes(),
                ));
            }
        }
        input.sources.push(SourceInput::new(
            PackageKey("right-core@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            public_provider("infixr").into_bytes(),
        ));
        for (package, source) in diamond_sources("right", "right_core") {
            input.sources.push(SourceInput::new(
                PackageKey(package),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                source.into_bytes(),
            ));
        }
        input
    };

    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            world(root, ("left-core@0.1.0", public_provider("infixl")), true),
            None,
        )
        .unwrap();
    let first = compiler
        .compile_revision(parent)
        .expect("both public generic diamonds must compile together")
        .artifact
        .unwrap();
    assert_eq!(first.run_i64().unwrap(), 91);

    let observer = compiler
        .import_revision(
            world(right_root, ("left-core@unused", String::new()), false),
            Some(parent),
        )
        .unwrap();
    let observer_artifact = compiler
        .compile_revision(observer)
        .expect("the unrelated right diamond must compile independently")
        .artifact
        .unwrap();
    assert_eq!(observer_artifact.run_i64().unwrap(), 43);
    let observer_bytes = observer_artifact.canonical_bytes().to_vec();
    let cached_parent = compiler.interface_cache_stats();
    let right_provider = DependencyNode::Interface(ModuleKey {
        package: PackageKey("right-core@0.1.0".into()),
        path: "crate".into(),
    });
    let mut right_traces = Vec::new();
    for package in ["right-a@0.1.0", "right-b@0.1.0", "right-diamond@0.1.0"] {
        let node = DependencyNode::Interface(ModuleKey {
            package: PackageKey(package.into()),
            path: "crate".into(),
        });
        let trace = compiler
            .dependency_trace(parent, &node)
            .expect("the full parent must freeze every right-diamond interface");
        assert!(trace.dependencies.contains(&right_provider));
        right_traces.push((node, trace));
    }
    let left_top = DependencyNode::Interface(ModuleKey {
        package: PackageKey("left-diamond@0.1.0".into()),
        path: "crate".into(),
    });
    let left_parent = compiler
        .dependency_trace(parent, &left_top)
        .expect("the full parent must freeze the left diamond interface");

    let rejected_world = world(root, ("left-core@0.2.0", private_provider.into()), true);
    let rejected = compiler
        .import_revision(rejected_world.clone(), Some(parent))
        .unwrap();
    let error = compiler
        .compile_session(&compiler.open_session(rejected).unwrap())
        .expect_err("a private callable/effect/GAT revision must reject its left diamond");
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3304"),
        "the changed private callable alias must be diagnosed: {:#?}",
        error.diagnostics()
    );
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3310"),
        "the changed private generic trait/GAT must be diagnosed: {:#?}",
        error.diagnostics()
    );
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3315"),
        "the changed private generic effect must be diagnosed: {:#?}",
        error.diagnostics()
    );
    assert!(
        error
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code != "G4111"),
        "private left fallout must not alter the independent right fixity world: {:#?}",
        error.diagnostics()
    );
    assert_eq!(compiler.interface_cache_stats(), cached_parent);
    assert!(compiler.dependency_traces(rejected).is_empty());
    for (node, trace) in &right_traces {
        assert_eq!(compiler.dependency_trace(parent, node), Some(trace.clone()));
    }
    let mut reordered_rejected = rejected_world;
    reordered_rejected.sources.reverse();
    assert_eq!(
        error.diagnostics(),
        StageZeroCompiler::new()
            .compile(reordered_rejected)
            .expect_err("source order cannot publish private left aliases")
            .diagnostics(),
        "private left-diamond diagnostics must be canonical"
    );
    let observer_replay = compiler.compile_revision(observer).unwrap().artifact.unwrap();
    assert_eq!(observer_replay.canonical_bytes(), observer_bytes.as_slice());

    let repaired = compiler
        .import_revision(
            world(root, ("left-core@0.2.0", public_provider("infixr")), true),
            Some(parent),
        )
        .unwrap();
    let repaired_artifact = compiler
        .compile_revision(repaired)
        .expect("a repaired left provider must not retain private diagnostics")
        .artifact
        .unwrap();
    assert_eq!(repaired_artifact.run_i64().unwrap(), 95);
    assert_ne!(first.fingerprint(), repaired_artifact.fingerprint());
    for (node, trace) in right_traces {
        let repaired_trace = compiler
            .dependency_trace(repaired, &node)
            .expect("the repaired world must retain every right-diamond interface");
        assert_eq!(
            repaired_trace.fingerprint, trace.fingerprint,
            "repairing the left diamond must not change a right-diamond interface identity"
        );
        assert_eq!(repaired_trace.dependencies, trace.dependencies);
    }
    let repaired_left = compiler
        .dependency_trace(repaired, &left_top)
        .expect("the repaired left facade must publish");
    assert_ne!(left_parent.fingerprint, repaired_left.fingerprint);
    assert!(compiler.interface_cache_stats().misses > cached_parent.misses);
}

#[test]
fn service_distinguishes_provider_identities_through_parallel_package_module_cycles() {
    let root = "use left_facade::{Capability as LeftCapability, Trace as LeftTrace}; use right_facade::{Capability as RightCapability, Trace as RightTrace}; pub struct LeftPacket { value: <i64 as LeftCapability<i64>>::Item<i64> } pub struct RightPacket { value: <i64 as RightCapability<i64>>::Item<i64> } pub fn left_worker() -> i64 / LeftTrace<i64> { let packet = LeftPacket { value: LeftCapability<i64>::relay(0, 41) }; LeftTrace<i64>::note(packet.value) } pub fn right_worker() -> i64 / RightTrace<i64> { let packet = RightPacket { value: RightCapability<i64>::relay(0, 41) }; RightTrace<i64>::note(packet.value) } pub fn left_value() -> i64 { handle left_worker() { LeftTrace<i64>::note(value) with k => k(value + 1) } } pub fn right_value() -> i64 { handle right_worker() { RightTrace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { left_value() + right_value() }";
    let public_provider = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let private_provider = "effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let world = |providers: Vec<(&str, &str)>, left_alias: &str, right_alias: &str| {
        let mut input = request(root);
        for (package, source) in providers {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                source.as_bytes(),
            ));
        }
        for (package, alias) in [
            ("left-facade@0.1.0", left_alias),
            ("right-facade@0.1.0", right_alias),
        ] {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                b"pub mod mirror; pub use crate::mirror::*;".as_slice(),
            ));
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/mirror/mirror.glorious").unwrap(),
                format!(
                    "pub use crate::*; pub use {alias}::{{Callback, Child as Capability, Trace}};"
                )
                .into_bytes(),
            ));
        }
        input
    };

    let compiler = StageZeroCompiler::new();
    let same = world(
        vec![("semantic-core@0.1.0", public_provider)],
        "semantic_core",
        "semantic_core",
    );
    let parent = compiler.import_revision(same.clone(), None).unwrap();
    let same_artifact = compiler
        .compile_revision(parent)
        .expect("parallel facade module cycles may share one provider identity")
        .artifact
        .unwrap();
    assert_eq!(same_artifact.run_i64().unwrap(), 86);
    let same_provider = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-core@0.1.0".into()),
        path: "crate".into(),
    });
    for package in ["left-facade@0.1.0", "right-facade@0.1.0"] {
        let trace = compiler
            .dependency_trace(
                parent,
                &DependencyNode::Interface(ModuleKey {
                    package: PackageKey(package.into()),
                    path: "crate::mirror".into(),
                }),
            )
            .expect("every facade mirror must freeze one interface");
        assert!(trace.dependencies.contains(&same_provider));
    }
    let mut reordered = same;
    reordered.sources.reverse();
    let same_reordered = compiler.import_revision(reordered, Some(parent)).unwrap();
    assert_eq!(same_reordered, parent);
    let reordered_artifact = compiler
        .compile_revision(same_reordered)
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(same_artifact.fingerprint(), reordered_artifact.fingerprint());
    assert_eq!(same_artifact.canonical_bytes(), reordered_artifact.canonical_bytes());

    let distinct = world(
        vec![
            ("alpha-core@0.1.0", public_provider),
            ("beta-core@0.1.0", public_provider),
        ],
        "alpha_core",
        "beta_core",
    );
    let child = compiler.import_revision(distinct, Some(parent)).unwrap();
    let distinct_artifact = compiler
        .compile_revision(child)
        .expect("same-spelled distinct providers must remain independently usable")
        .artifact
        .unwrap();
    assert_eq!(distinct_artifact.run_i64().unwrap(), 86);
    assert_ne!(same_artifact.fingerprint(), distinct_artifact.fingerprint());
    assert_ne!(same_artifact.canonical_bytes(), distinct_artifact.canonical_bytes());

    let private = world(
        vec![
            ("alpha-core@0.1.0", public_provider),
            ("beta-core@0.1.0", private_provider),
        ],
        "alpha_core",
        "beta_core",
    );
    let cached = compiler.interface_cache_stats();
    let private_child = compiler.import_revision(private, Some(child)).unwrap();
    let session = compiler.open_session(private_child).unwrap();
    let error = compiler
        .compile_session(&session)
        .expect_err("a private provider cannot leak through its cyclic public facade");
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "private provider authority must retain its public-import rejection: {:#?}",
        error.diagnostics()
    );
    assert!(
        error
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code != "G4111"),
        "private visibility fallout must not turn into a provider-fixity ambiguity: {:#?}",
        error.diagnostics()
    );
    assert_eq!(compiler.interface_cache_stats(), cached);
    assert!(compiler.dependency_traces(private_child).is_empty());
}

#[test]
fn service_seals_generic_fixity_identity_through_parallel_package_module_cycles() {
    let root = "use left_facade::*; use right_facade::{Child as RightCapability, Trace as RightTrace}; pub struct LeftPacket { value: <i64 as Child<i64>>::Item<i64> } pub struct RightPacket { value: <i64 as RightCapability<i64>>::Item<i64> } pub fn left_worker() -> i64 / Trace<i64> { let packet = LeftPacket { value: Child<i64>::relay(0, 41) }; Trace<i64>::note(packet.value) } pub fn right_worker() -> i64 / RightTrace<i64> { let packet = RightPacket { value: RightCapability<i64>::relay(0, 41) }; RightTrace<i64>::note(packet.value) } pub fn left_value() -> i64 { handle left_worker() { Trace<i64>::note(value) with k => k(value + 1) } } pub fn right_value() -> i64 { handle right_worker() { RightTrace<i64>::note(value) with k => k(value + 1) } } pub fn main() -> i64 { 10 ** 3 ** 2 + left_value() + right_value() }";
    let public_provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let private_provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    let world = |providers: Vec<(&str, &str)>, left_alias: &str, right_alias: &str| {
        let mut input = request(root);
        for (package, source) in providers {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                source.as_bytes(),
            ));
        }
        for (package, alias) in [
            ("left-facade@0.1.0", left_alias),
            ("right-facade@0.1.0", right_alias),
        ] {
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                b"pub mod mirror; pub use crate::mirror::*;".as_slice(),
            ));
            input.sources.push(SourceInput::new(
                PackageKey(package.into()),
                LogicalPath::parse("src/mirror/mirror.glorious").unwrap(),
                format!("pub use crate::*; pub use {alias}::*;").into_bytes(),
            ));
        }
        input
    };

    let compiler = StageZeroCompiler::new();
    let shared = world(
        vec![("semantic-core@0.1.0", public_provider)],
        "semantic_core",
        "semantic_core",
    );
    let parent = compiler.import_revision(shared.clone(), None).unwrap();
    let shared_artifact = compiler
        .compile_revision(parent)
        .expect("parallel cycles must preserve one shared generic operator identity")
        .artifact
        .unwrap();
    assert_eq!(shared_artifact.run_i64().unwrap(), 95);
    let shared_provider = DependencyNode::Interface(ModuleKey {
        package: PackageKey("semantic-core@0.1.0".into()),
        path: "crate".into(),
    });
    for package in ["left-facade@0.1.0", "right-facade@0.1.0"] {
        let trace = compiler
            .dependency_trace(
                parent,
                &DependencyNode::Interface(ModuleKey {
                    package: PackageKey(package.into()),
                    path: "crate::mirror".into(),
                }),
            )
            .expect("every cyclic facade mirror must publish an interface");
        assert!(
            trace.dependencies.contains(&shared_provider),
            "{package} must retain the shared provider's generic operator identity"
        );
    }
    let cached_shared = compiler.interface_cache_stats();
    let mut reordered_shared = shared;
    reordered_shared.sources.reverse();
    let replay = compiler.import_revision(reordered_shared, Some(parent)).unwrap();
    assert_eq!(replay, parent, "source order must not split the shared provider world");
    let replay_artifact = compiler.compile_revision(replay).unwrap().artifact.unwrap();
    assert_eq!(shared_artifact.fingerprint(), replay_artifact.fingerprint());
    assert_eq!(shared_artifact.canonical_bytes(), replay_artifact.canonical_bytes());
    assert_eq!(compiler.interface_cache_stats().misses, cached_shared.misses);

    let distinct = world(
        vec![
            ("alpha-core@0.1.0", public_provider),
            ("beta-core@0.1.0", public_provider),
        ],
        "alpha_core",
        "beta_core",
    );
    let child = compiler.import_revision(distinct, Some(parent)).unwrap();
    let distinct_artifact = compiler
        .compile_revision(child)
        .expect("same-named generic provider contracts must remain distinct by package identity")
        .artifact
        .unwrap();
    assert_eq!(distinct_artifact.run_i64().unwrap(), 95);
    assert_ne!(shared_artifact.fingerprint(), distinct_artifact.fingerprint());
    assert_ne!(shared_artifact.canonical_bytes(), distinct_artifact.canonical_bytes());

    let private = world(
        vec![
            ("alpha-core@0.1.0", public_provider),
            ("beta-core@0.1.0", private_provider),
        ],
        "alpha_core",
        "beta_core",
    );
    let cached = compiler.interface_cache_stats();
    let private_child = compiler.import_revision(private.clone(), Some(child)).unwrap();
    let error = compiler
        .compile_session(&compiler.open_session(private_child).unwrap())
        .expect_err("a private generic provider cannot cross its cyclic facade");
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3326"),
        "the private branch must reject its facade imports: {:#?}",
        error.diagnostics()
    );
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3315"),
        "the private branch must retain its private-effect authority error: {:#?}",
        error.diagnostics()
    );
    assert!(
        error
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code != "G4111"),
        "private provider fallout must not leak into public operator grouping: {:#?}",
        error.diagnostics()
    );
    assert_eq!(compiler.interface_cache_stats(), cached);
    assert!(compiler.dependency_traces(private_child).is_empty());
    let mut reordered_private = private;
    reordered_private.sources.reverse();
    let second = StageZeroCompiler::new()
        .compile(reordered_private)
        .expect_err("source order cannot expose a private generic provider");
    assert_eq!(
        error.diagnostics(),
        second.diagnostics(),
        "private parallel-cycle diagnostics must be canonical"
    );
}

#[test]
fn service_rejects_private_associated_item_and_callable_alias_reexports_before_grouping() {
    let mut request = request("use top_facade::*; pub fn main() -> i64 { 10 ** 3 ** 2 }");
    let provider = "pub infixr 30 **; pub trait Combine<T> { **(left: T, right: T) -> T; } impl Combine<i64> for i64 { **(left: i64, right: i64) -> i64 { left - right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> i64 / {Trace<U>} { Trace<U>::note(value) } } impl Child<i64> for i64 {} type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> };";
    for (package, source) in [
        ("semantic-core@0.1.0", provider),
        (
            "middle-facade@0.1.0",
            "pub use semantic_core::{Callback, Child as Capability, Trace}; pub use semantic_core::*;",
        ),
        ("top-facade@0.1.0", "pub use middle_facade::*;"),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let mut reordered = request.clone();
    reordered.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(first)) = StageZeroCompiler::new().compile(request)
    else {
        panic!("private associated items or callable aliases unexpectedly crossed facades");
    };
    let Err(grandiose_stage0::ServiceError::Failed(second)) =
        StageZeroCompiler::new().compile(reordered)
    else {
        panic!("source ordering changed private facade authority into success");
    };
    assert!(
        first.iter().any(|diagnostic| diagnostic.code == "G3317"),
        "missing private associated-item/callable-alias authority diagnostic: {first:#?}"
    );
    assert!(
        first.iter().all(|diagnostic| diagnostic.code == "G3317"),
        "private facade authority must fail before operator grouping: {first:#?}"
    );
    assert_eq!(first, second, "private associated-item diagnostics must be canonical");
}

#[test]
fn service_rejects_partial_multilevel_operator_reexports_before_grouping() {
    let mut request = request("use top_facade::*; pub fn main() -> i64 { 10 ** 3 ** 2 }");
    let provider = "pub infixr 30 **; trait Combine { **(left: i64, right: i64) -> i64; } impl Combine for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub type Callback<U> = (i64, U) -> i64 / {Trace<U>};";
    for (package, source) in [
        ("semantic-core@0.1.0", provider),
        (
            "middle-facade@0.1.0",
            "pub use semantic_core::Combine; pub use semantic_core::*;",
        ),
        ("top-facade@0.1.0", "pub use middle_facade::*;"),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let mut reordered = request.clone();
    reordered.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(first)) = StageZeroCompiler::new().compile(request)
    else {
        panic!("a private operator trait unexpectedly reached expression grouping");
    };
    let Err(grandiose_stage0::ServiceError::Failed(second)) =
        StageZeroCompiler::new().compile(reordered)
    else {
        panic!("source ordering changed partial operator authority into success");
    };
    assert!(
        first.iter().any(|diagnostic| diagnostic.code == "G3317"),
        "missing partial operator re-export authority diagnostic: {first:#?}"
    );
    assert!(
        first.iter().all(|diagnostic| diagnostic.code == "G3317"),
        "partial authority must fail before body grouping diagnostics: {first:#?}"
    );
    assert_eq!(first, second, "partial re-export diagnostics must be canonical");
}

#[test]
fn service_reports_distinct_provider_reexported_fixities_canonically() {
    let mut request = request("use left_facade::*; use right_facade::*; pub fn main() -> i64 { 1 ** 2 }");
    let alpha = "pub infixl 30 **; pub trait Combine { **(left: i64, right: i64) -> i64; } impl Combine for i64 { **(left: i64, right: i64) -> i64 { left + right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Capability<T> { type Effects<U>: EffectRow; } impl Capability<i64> for i64 { type Effects<U> = {Trace<U>}; }";
    let beta = "pub infixr 30 **; pub trait Combine { **(left: i64, right: i64) -> i64; } impl Combine for i64 { **(left: i64, right: i64) -> i64 { left - right } } pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Capability<T> { type Effects<U>: EffectRow; } impl Capability<i64> for i64 { type Effects<U> = {Trace<U>}; }";
    for (package, source) in [
        ("alpha-core@0.1.0", alpha),
        ("beta-core@0.1.0", beta),
        ("left-facade@0.1.0", "pub use alpha_core::*;"),
        ("right-facade@0.1.0", "pub use beta_core::*;"),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let mut reordered = request.clone();
    reordered.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(first)) = StageZeroCompiler::new().compile(request)
    else {
        panic!("distinct re-exported fixities unexpectedly chose an operator grouping");
    };
    let Err(grandiose_stage0::ServiceError::Failed(second)) =
        StageZeroCompiler::new().compile(reordered)
    else {
        panic!("source ordering changed fixity ambiguity into success");
    };
    assert!(
        first
            .iter()
            .any(|diagnostic| diagnostic.code == "G4111" && diagnostic.message.contains("ambiguous")),
        "missing re-exported provider-fixity ambiguity: {first:#?}"
    );
    assert_eq!(first, second, "re-exported fixity diagnostics must be canonical");
}

#[test]
fn service_rejects_private_generic_reexports_despite_public_operator_authority() {
    let mut request = request("pub fn main() -> i64 { 42 }");
    let provider = "pub infixl 30 **; pub trait Combine { **(left: i64, right: i64) -> i64; } impl Combine for i64 { **(left: i64, right: i64) -> i64 { left + right } } effect Trace<T> { [1,1] note(value: T) -> i64; } trait Capability<T> { type Effects<U>: EffectRow; } impl Capability<i64> for i64 { type Effects<U> = {Trace<U>}; }";
    for (package, source) in [
        ("semantic-core@0.1.0", provider),
        (
            "left-facade@0.1.0",
            "pub use semantic_core::{Capability, Trace}; pub use semantic_core::{Combine, **};",
        ),
        ("right-facade@0.1.0", "pub use semantic_core::{Combine, **};"),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source.as_bytes(),
        ));
    }
    let mut reordered = request.clone();
    reordered.sources.reverse();
    let Err(grandiose_stage0::ServiceError::Failed(first)) = StageZeroCompiler::new().compile(request)
    else {
        panic!("public operator authority unexpectedly exposed private generic contracts");
    };
    let Err(grandiose_stage0::ServiceError::Failed(second)) =
        StageZeroCompiler::new().compile(reordered)
    else {
        panic!("source ordering changed private re-export rejection into success");
    };
    assert!(
        first.iter().any(|diagnostic| diagnostic.code == "G3317"),
        "missing private generic re-export authority diagnostic: {first:#?}"
    );
    assert_eq!(first, second, "private re-export diagnostics must be canonical");
}

#[test]
fn service_materializes_reachable_generic_dependency_callables() {
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::identity; pub fn main() -> i64 { identity(42) }",
            "math@0.1.0",
            "pub fn identity<T>(value: T) -> T { value }",
        ))
        .expect("a reachable generic dependency body must materialize into the linked artifact");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_imported_reference_lifetimes_through_closures_and_handlers() {
    // The dependency signature carries the exact input/output lifetime
    // relation.  It must remain valid when the result is captured by a local
    // closure and invoked from a handler clause, while the same relation must
    // still reject a returned closure that would outlive its body-local loan.
    let dependency = "pub fn relay<'a>(value: &'a i64) -> &'a i64 { value }";
    let accepted = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::relay; effect Tick { [0,1] tick() -> i64; } pub fn main() -> i64 { let value = 41; let callback = () -> i64 { *relay(&value) + 1 }; handle Tick::tick() { Tick::tick() with _ => callback() } }",
            "math@0.1.0",
            dependency,
        ))
        .expect("an imported reference may stay live inside a local handler closure");
    assert!(
        accepted.diagnostics.is_empty(),
        "{:#?}",
        accepted.diagnostics
    );
    assert_eq!(accepted.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = StageZeroCompiler::new().compile(request_with_dependency(
        "use math::relay; pub fn bad() -> () -> &i64 { let value = 1; let borrowed = relay(&value); () -> &i64 { borrowed } } pub fn main() -> i64 { 0 }",
        "math@0.1.0",
        dependency,
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = rejected else {
        panic!("an imported body-local borrow unexpectedly escaped through a closure");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5014"),
        "missing imported closure-lifetime escape diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_enforces_move_captured_callable_use_through_dependency_handlers() {
    // The callback capture is owned by the handler arm, then transferred to a
    // dependency callable.  A single transfer is valid; invoking that same
    // captured closure twice must not be hidden by the package boundary or
    // handler environment.
    let dependency = "pub fn invoke(callback: () -> i64) -> i64 { callback() }";
    let accepted = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::invoke; effect Tick { [0,1] tick() -> i64; } pub fn next(value: i64) -> i64 { value + 1 } pub fn run(function: (i64) -> i64) -> i64 { let callback = () -> i64 { move function(41) }; handle Tick::tick() { Tick::tick() with _ => invoke(callback) } } pub fn main() -> i64 { run(next) }",
            "math@0.1.0",
            dependency,
        ))
        .expect("one move-captured callback transfer through a dependency handler must work");
    assert!(
        accepted.diagnostics.is_empty(),
        "{:#?}",
        accepted.diagnostics
    );
    assert_eq!(accepted.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = StageZeroCompiler::new().compile(request_with_dependency(
        "use math::invoke; effect Tick { [0,1] tick() -> i64; } pub fn next(value: i64) -> i64 { value + 1 } pub fn run(function: (i64) -> i64) -> i64 { let callback = () -> i64 { move function(41) }; handle Tick::tick() { Tick::tick() with _ => invoke(callback) + invoke(callback) } } pub fn main() -> i64 { run(next) }",
        "math@0.1.0",
        dependency,
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = rejected else {
        panic!("a move-captured callback was unexpectedly consumed twice through a dependency");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing cross-package move-capture use diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_preserves_generic_dependency_effect_identity_through_replay() {
    // The imported generic effect must be instantiated once as `Ask<i64>`
    // across the dependency callable, the caller's handler frame, and both
    // replayed continuation invocations.  A same-spelled `Ask<Text>` handler
    // cannot discharge that outward effect.
    let dependency = "pub effect Ask<T> { [2,2] ask(value: T) -> T; } pub fn relay<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) }";
    let accepted = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::Ask; use math::relay; pub fn main() -> i64 { handle relay(20) { Ask<i64>::ask(value, k) => k(value) + k(value + 1) } }",
            "math@0.1.0",
            dependency,
        ))
        .expect("a generic dependency performance must replay through its exact handler instance");
    assert!(
        accepted.diagnostics.is_empty(),
        "{:#?}",
        accepted.diagnostics
    );
    assert_eq!(accepted.artifact.unwrap().run_i64().unwrap(), 41);

    let rejected = StageZeroCompiler::new().compile(request_with_dependency(
        "use math::Ask; use math::relay; pub fn main() -> i64 { handle relay(20) { Ask<Text>::ask(value, k) => k(\"wrong\") + k(\"instance\") } }",
        "math@0.1.0",
        dependency,
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = rejected else {
        panic!("a mismatched generic dependency handler unexpectedly closed Ask<i64>");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "mismatched imported effect instance must remain outward: {diagnostics:#?}"
    );
}

#[test]
fn service_links_private_generic_nested_handler_replay_bodies_from_dependencies() {
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::Tick; use math::relay; pub fn main() -> i64 { handle relay(41) { Tick::tick() with k => k(0) } }",
            "math@0.1.0",
            "pub effect Ask<T> { [2,2] ask(value: T) -> T; } pub effect Tick { [1,1] tick() -> i64; } fn leaf<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) } pub fn relay(value: i64) -> i64 / Tick { handle leaf<i64>(value) { Ask<i64>::ask(found) with k => { Tick::tick(); k(found) + k(found + 1) } } }",
        ))
        .expect("a linked dependency must retain private generic leaf and nested replay handler bodies");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn service_restores_nested_replay_contexts_through_dependency_facade_bodies() {
    let mut request = request(
        "use bridge::Tick; use bridge::relay; pub fn main() -> i64 { handle relay(41) { Tick::tick() with k => k(0) + k(1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Tick, relay};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"effect Ask<T> { [2,2] ask(value: T) -> T; } pub effect Tick { [2,2] tick() -> i64; } fn leaf<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) } pub fn relay(value: i64) -> i64 / Tick { handle leaf<i64>(value) { Ask<i64>::ask(found) with k => { Tick::tick(); k(found) + k(found + 1) } } }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("nested replay frames must retain the private generic dependency body");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 166);
}

#[test]
fn service_executes_local_generic_nested_handler_replay_with_an_outer_effect() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "effect Ask<T> { [2,2] ask(value: T) -> T; } effect Tick { [1,1] tick() -> i64; } fn leaf<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) } pub fn relay(value: i64) -> i64 / Tick { handle leaf<i64>(value) { Ask<i64>::ask(found) with k => { Tick::tick(); k(found) + k(found + 1) } } } pub fn main() -> i64 { handle relay(41) { Tick::tick() with k => k(0) } }",
        ))
        .expect("the local control shape must compile before dependency linking is considered");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn service_preserves_generic_effect_identity_through_dependency_reexport_facades() {
    let public = {
        let mut request = request(
            "use bridge::Ask; use bridge::relay; pub fn main() -> i64 { handle relay(20) { Ask<i64>::ask(value, k) => k(value) + k(value + 1) } }",
        );
        request.sources.push(SourceInput::new(
            PackageKey("bridge@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"pub use provider::{Ask, relay};".as_slice(),
        ));
        request.sources.push(SourceInput::new(
            PackageKey("provider@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"pub effect Ask<T> { [2,2] ask(value: T) -> T; } pub fn relay<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) }".as_slice(),
        ));
        StageZeroCompiler::new().compile(request)
    };
    let public = public.expect(
        "a generic effect reexport must retain one instantiated operation identity through replay",
    );
    assert!(public.diagnostics.is_empty(), "{:#?}", public.diagnostics);
    assert_eq!(public.artifact.unwrap().run_i64().unwrap(), 41);

    let private = {
        let mut request = request("pub fn main() -> i64 { 42 }");
        request.sources.push(SourceInput::new(
            PackageKey("bridge@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"pub use provider::{Ask, relay};".as_slice(),
        ));
        request.sources.push(SourceInput::new(
            PackageKey("provider@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"effect Ask<T> { [2,2] ask(value: T) -> T; } pub fn relay<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) }".as_slice(),
        ));
        StageZeroCompiler::new().compile(request)
    };
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = private else {
        panic!("a private generic effect unexpectedly leaked through a public facade")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "missing private generic-effect facade diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_forwards_a_partial_local_handler_over_an_imported_deep_effect() {
    let dependency = "pub effect Ask { [1,1] ask(value: Bool) -> i64; } pub fn relay(value: Bool) -> i64 / Ask { Ask::ask(value) }";
    let root = "use dependency::Ask; use dependency::relay; pub fn main() -> i64 { handle { handle relay(false) { Ask::ask(true) with k => k(40) } } { Ask::ask(value) with k => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request_with_dependency(root, "dependency@0.1.0", dependency)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_cancels_an_optional_generic_dependency_resumption() {
    // Cancellation has a separate runtime edge from replay.  Keep the effect
    // and generic helper in a dependency so the imported `Ask<i64>` identity
    // and its optional continuation contract must survive linking before the
    // caller can consume the continuation with a cancellation clause.
    let dependency = "pub effect Ask<T> { [0,1] ask(value: T) -> T; } pub fn relay<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::Ask; use math::relay; pub fn main() -> i64 { handle relay(20) { Ask<i64>::ask(_) with _ => 42 } }",
            "math@0.1.0",
            dependency,
        ))
        .expect("an optional generic dependency continuation must be cancellable");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_cancels_a_second_imported_operation_after_resuming_the_first() {
    let dependency = "pub effect Console { [1,1] read(value: i64) -> i64; [0,1] write(value: i64) -> i64; } pub fn relay(value: i64) -> i64 / Console { let read = Console::read(value); Console::write(read) }";
    let root = "use dependency::Console; use dependency::relay; pub fn main() -> i64 { handle relay(40) { Console::read(value) with k => k(value + 1); Console::write(_) with _ => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request_with_dependency(
        root,
        "dependency@0.1.0",
        dependency,
    ));
    let outcome = outcome.expect("a resumed imported call should reach its cancellation arm");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_replays_a_forwarded_imported_read_then_cancels_its_nested_write() {
    let dependency = "pub effect Console { [2,2] read(value: Bool) -> i64; [0,1] write(value: i64) -> i64; } pub fn relay(value: Bool) -> i64 / Console { let read = Console::read(value); Console::write(read) }";
    let root = "use dependency::Console; use dependency::relay; pub fn main() -> i64 { handle { handle relay(false) { Console::read(true) with k => k(1) + k(2); Console::write(_) with _ => 40 } } { Console::read(_) with k => k(20) + k(21) } }";
    let outcome = StageZeroCompiler::new().compile(request_with_dependency(
        root,
        "dependency@0.1.0",
        dependency,
    ));
    let outcome = outcome.expect("nested partial replay and cancellation should cross a dependency call");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 80);
}

#[test]
fn service_replays_through_two_partial_facade_handlers_before_nested_cancellation() {
    let mut request = request(
        "use bridge::Console; use bridge::invoke; pub fn main() -> i64 { handle { handle { handle invoke(false) { Console::read(true) with k => k(1) + k(2); Console::write(_) with _ => 40 } } { Console::read(true) with k => k(3) + k(4) } } { Console::read(_) with k => k(20) + k(21) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Console, relay}; pub fn invoke(value: Bool) -> i64 / Console { relay(value) }".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Console { [2,2] read(value: Bool) -> i64; [0,1] write(value: i64) -> i64; } pub fn relay(value: Bool) -> i64 / Console { let read = Console::read(value); Console::write(read) }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new().compile(request);
    let outcome = outcome.expect("nested facade replay and cancellation should cross caller frames");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 80);
}

#[test]
fn service_replays_nested_facade_cancellation_through_outer_normal_completion() {
    // Each outer replay enters the imported relay through the public facade,
    // forwards across both refutable inner handlers, then reaches the inner
    // cancellation arm. The outer normal-completion clause must run once per
    // replayed path, after the cancellation unwinds the inactive lower frames.
    let mut request = request(
        "use bridge::Console; use bridge::invoke; pub fn main() -> i64 { handle { handle { handle invoke(false) { Console::read(true) with k => k(1) + k(2); Console::write(_) with _ => 40 } } { Console::read(true) with k => k(3) + k(4) } } { value => value + 1; Console::read(_) with k => k(20) + k(21) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Console, relay}; pub fn invoke(value: Bool) -> i64 / Console { relay(value) }".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Console { [2,2] read(value: Bool) -> i64; [0,1] write(value: i64) -> i64; } pub fn relay(value: Bool) -> i64 / Console { let read = Console::read(value); Console::write(read) }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new().compile(request);
    let outcome = outcome.expect("completion must run after each replayed facade cancellation");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 82);
}

#[test]
fn service_replays_effectful_completion_after_facade_cancellation_through_outer_resume() {
    // The completion arm is executed on each replayed residual after the
    // inner write cancellation. It crosses bridge::record -> provider::audit
    // before an outer Audit handler resumes that ordinary call stack.
    let mut request = request(
        "use bridge::Audit; use bridge::Console; use bridge::invoke; use bridge::record; pub fn main() -> i64 { handle { handle { handle { handle invoke(false) { Console::read(true) with k => k(1) + k(2); Console::write(_) with _ => 40 } } { Console::read(true) with k => k(3) + k(4) } } { value => { let audited = record(value); audited + 1 }; Console::read(_) with k => k(20) + k(21) } } { Audit::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Audit, Console, audit, relay}; pub fn invoke(value: Bool) -> i64 / Console { relay(value) } pub fn record(value: i64) -> i64 / Audit { audit(value) }".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Console { [2,2] read(value: Bool) -> i64; [0,1] write(value: i64) -> i64; } pub effect Audit { [1,1] note(value: i64) -> i64; } pub fn relay(value: Bool) -> i64 / Console { let read = Console::read(value); Console::write(read) } pub fn audit(value: i64) -> i64 / Audit { Audit::note(value) }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new().compile(request);
    let outcome = outcome.expect("effectful completion must resume through the facade caller frames");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 84);
}

#[test]
fn service_reentrant_tick_resume_forwards_nested_facade_ask_through_completion() {
    let mut request = request(
        "use bridge::Ask; use bridge::Tick; use bridge::invoke; pub fn main() -> i64 { handle { handle { handle invoke() { Ask::ask(true) with k => k(1) + k(2) } } { value => value + 1; Tick::tick() with k => k(10) + k(20) } } { Ask::ask(_) with k => k(30) + k(40) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Ask, Tick, relay}; pub fn invoke() -> i64 / {Ask, Tick} { relay() }"
            .as_slice(),
    ));
    request.sources.push(SourceInput::new(PackageKey("provider@0.1.0".into()), LogicalPath::parse("src/lib.glorious").unwrap(), b"pub effect Ask { [2,2] ask(value: Bool) -> i64; } pub effect Tick { [2,2] tick() -> i64; } pub fn relay() -> i64 / {Ask, Tick} { let tick = Tick::tick(); let asked = Ask::ask(false); tick + asked }".as_slice()));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("reentrant replay must execute");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 204);
}

#[test]
fn service_reentrant_completion_cancels_to_label_through_nested_facades() {
    // A replayed Console residual first completes through the outer normal
    // arm, which re-enters the separate Audit handler through bridge::record.
    // That handler cancels its continuation by leaving the surrounding label.
    let mut request = request(
        "use bridge::Ask; use bridge::Audit; use bridge::Tick; use bridge::invoke; use bridge::record; pub fn main() -> i64 { label done { handle { handle { handle { handle invoke() { Ask::ask(true) with k => k(1) + k(2) } } { value => { let audited = record(value); audited + 1 }; Tick::tick() with k => k(10) + k(20) } } { Ask::ask(_) with k => k(30) + k(40) } } { Audit::note(value, _) => transfer done value } } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Ask, Audit, Tick, audit, relay}; pub fn invoke() -> i64 / {Ask, Tick} { relay() } pub fn record(value: i64) -> i64 / Audit { audit(value) }".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Ask { [2,2] ask(value: Bool) -> i64; } pub effect Tick { [2,2] tick() -> i64; } pub effect Audit { [0,1] note(value: i64) -> i64; } pub fn relay() -> i64 / {Ask, Tick} { let tick = Tick::tick(); let asked = Ask::ask(false); tick + asked } pub fn audit(value: i64) -> i64 / Audit { Audit::note(value) }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("reentrant completion cancellation must execute through dependency facades");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 40);
}

#[test]
fn service_outer_completion_leaves_after_reentrant_forwarded_replay_through_facades() {
    // Each Tick replay reaches the refutable inner Ask row, forwards its
    // pending continuation to the outer Ask replayer, and only then finishes
    // the enclosing computation. The outer normal-completion arm leaves the
    // label, abandoning its remaining replay and forwarded-frame suffix.
    let mut request = request(
        "use bridge::Ask; use bridge::Tick; use bridge::invoke; pub fn main() -> i64 { label done { handle { handle { handle { handle invoke() { Ask::ask(true) with k => k(1) + k(2) } } { value => value + 1; Tick::tick() with k => k(10) + k(20) } } { Ask::ask(_) with k => k(30) + k(40) } } { value => transfer done value } } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Ask, Tick, relay}; pub fn invoke() -> i64 / {Ask, Tick} { relay() }"
            .as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Ask { [2,2] ask(value: Bool) -> i64; } pub effect Tick { [2,2] tick() -> i64; } pub fn relay() -> i64 / {Ask, Tick} { let tick = Tick::tick(); let asked = Ask::ask(false); tick + asked }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("outer completion leave must abandon forwarded replay state");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_inner_reentrant_completion_leave_retains_outer_normal_completion_through_facades() {
    // The inner completion leaves `done` after the first forwarded replayed
    // residual. That leave ends only the inner label: the surrounding
    // non-replayed completion must still observe the label result and add 100.
    let mut request = request(
        "use bridge::Ask; use bridge::Tick; use bridge::invoke; pub fn main() -> i64 { handle { label done { handle { handle { handle { handle invoke() { Ask::ask(true) with k => k(1) + k(2) } } { value => value + 1; Tick::tick() with k => k(10) + k(20) } } { Ask::ask(_) with k => k(30) + k(40) } } { value => transfer done value } } } { value => value + 100 } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Ask, Tick, relay}; pub fn invoke() -> i64 / {Ask, Tick} { relay() }"
            .as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Ask { [2,2] ask(value: Bool) -> i64; } pub effect Tick { [2,2] tick() -> i64; } pub fn relay() -> i64 / {Ask, Tick} { let tick = Tick::tick(); let asked = Ask::ask(false); tick + asked }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("inner completion leave must preserve the outer completion");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 141);
}

#[test]
fn service_outer_replay_after_inner_label_leave_reenters_effectful_dependency_completion() {
    let mut request = request(
        "use bridge::Ask; use bridge::Audit; use bridge::Tick; use bridge::invoke; use bridge::record; pub fn main() -> i64 { handle { handle { label done { handle { handle { handle { handle invoke() { Ask::ask(true) with k => k(1) + k(2) } } { value => value + 1; Tick::tick() with k => k(10) + k(20) } } { Ask::ask(_) with k => k(30) + k(40) } } { value => transfer done value } } } { value => { let audited = record(value); audited + 100 } } } { Audit::note(_) with k => k(1) + k(2) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Ask, Audit, Tick, audit, relay}; pub fn invoke() -> i64 / {Ask, Tick} { relay() } pub fn record(value: i64) -> i64 / Audit { audit(value) }".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Ask { [2,2] ask(value: Bool) -> i64; } pub effect Tick { [2,2] tick() -> i64; } pub effect Audit { [2,2] note(value: i64) -> i64; } pub fn relay() -> i64 / {Ask, Tick} { let tick = Tick::tick(); let asked = Ask::ask(false); tick + asked } pub fn audit(value: i64) -> i64 / Audit { Audit::note(value) }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new().compile(request);
    let outcome = outcome.expect("outer replay must re-enter the retained effectful completion");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 203);
}

#[test]
fn service_links_private_helpers_reached_from_specialized_dependency_generics() {
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::relay; pub fn main() -> i64 { relay(42) }",
            "math@0.1.0",
            "fn helper<T>(value: T) -> T { value } pub fn relay<T>(value: T) -> T { helper(value) }",
        ))
        .expect("a specialized exported generic must retain its dependency-private helper body");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_links_transitive_dependency_callable_bodies() {
    let mut request = request("use middle::relay; pub fn main() -> i64 { relay() }");
    request.sources.push(SourceInput::new(
        PackageKey("middle@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"use base::answer; pub fn relay() -> i64 { answer() }".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("base@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub fn answer() -> i64 { 42 }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("transitive dependency callable bodies must link into the root artifact");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_ambiguous_dependency_fixity_imports() {
    let mut request = request("use left::*; use right::*; pub fn main() -> i64 { 1 ** 2 }");
    for (package, source) in [
        ("left@0.1.0", b"pub infixl 30 **;".as_slice()),
        ("right@0.1.0", b"pub infixr 30 **;".as_slice()),
    ] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            source,
        ));
    }
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("ambiguous imported fixity declarations unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4111" && diagnostic.message.contains("ambiguous")),
        "missing ambiguous imported-fixity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_enforces_cross_package_orphan_coherence_through_public_reexports() {
    let legal = {
        let mut request = request(
            "use bridge::ForeignTrait; pub struct Local {} impl ForeignTrait for Local { fn value(receiver: Local) -> i64 { 42 } } pub fn main() -> i64 { ForeignTrait::value(Local {}) }",
        );
        request.sources.push(SourceInput::new(
            PackageKey("bridge@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"pub use provider::ForeignTrait;".as_slice(),
        ));
        request.sources.push(SourceInput::new(
            PackageKey("provider@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"pub trait ForeignTrait { fn value(receiver: Self) -> i64; } pub struct ForeignType {};".as_slice(),
        ));
        StageZeroCompiler::new().compile(request)
    };
    let legal = legal.expect("a local self type must anchor an imported trait implementation");
    assert!(legal.diagnostics.is_empty(), "{:#?}", legal.diagnostics);
    assert_eq!(legal.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = {
        let mut request = request(
            "use bridge::{ForeignTrait, ForeignType}; impl ForeignTrait for ForeignType { fn value(receiver: ForeignType) -> i64 { 42 } } pub fn main() -> i64 { 0 }",
        );
        request.sources.push(SourceInput::new(
            PackageKey("bridge@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"pub use provider::{ForeignTrait, ForeignType};".as_slice(),
        ));
        request.sources.push(SourceInput::new(
            PackageKey("provider@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"pub trait ForeignTrait { fn value(receiver: Self) -> i64; } pub struct ForeignType {};".as_slice(),
        ));
        StageZeroCompiler::new().compile(request)
    };
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = rejected else {
        panic!("a foreign trait implementation for a foreign reexport unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3407"),
        "missing cross-package orphan diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_preserves_associated_item_authority_through_dependency_trait_facades() {
    let exported = {
        let mut request = request(
            "use bridge::Capability; pub fn relay(value: <i64 as Capability>::Item) -> <i64 as Capability>::Item { Capability::value(value) } pub fn main() -> i64 { relay(42) }",
        );
        request.sources.push(SourceInput::new(
            PackageKey("bridge@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"pub use provider::Capability;".as_slice(),
        ));
        request.sources.push(SourceInput::new(
            PackageKey("provider@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"pub trait Capability { type Item; fn value(receiver: Self) -> i64; } impl Capability for i64 { type Item = i64; fn value(receiver: i64) -> i64 { receiver } }".as_slice(),
        ));
        StageZeroCompiler::new().compile(request)
    };
    let exported = exported
        .expect("a public trait facade must preserve its associated-item contracts into Core");
    assert!(exported.diagnostics.is_empty(), "{:#?}", exported.diagnostics);
    assert_eq!(exported.artifact.unwrap().run_i64().unwrap(), 42);

    let private = {
        let mut request = request("pub fn main() -> i64 { 42 }");
        request.sources.push(SourceInput::new(
            PackageKey("bridge@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"pub use provider::Capability;".as_slice(),
        ));
        request.sources.push(SourceInput::new(
            PackageKey("provider@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            b"trait Capability { type Item; fn value(receiver: Self) -> i64; } impl Capability for i64 { type Item = i64; fn value(receiver: i64) -> i64 { receiver } }".as_slice(),
        ));
        StageZeroCompiler::new().compile(request)
    };
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = private else {
        panic!("a private dependency trait unexpectedly leaked its associated-item API")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "missing private associated-item facade diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_materializes_dependency_generic_function_values_for_indirect_calls() {
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::identity; pub fn apply(function: (i64) -> i64) -> i64 { function(42) } pub fn main() -> i64 { apply(identity) }",
            "math@0.1.0",
            "pub fn identity<T>(value: T) -> T { value }",
        ))
        .expect("generic dependency function values must be materialized before indirect execution");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_dependency_generic_trait_method_values_for_indirect_calls() {
    let outcome = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::Replace; pub fn apply(function: (i64, Text) -> Text) -> Text { function(0, \"linked\") } pub fn main() -> Text { apply(Replace::replace) }",
            "math@0.1.0",
            "pub trait Replace { fn replace<T>(value: i64, replacement: T) -> T; } impl Replace for i64 { fn replace<T>(value: i64, replacement: T) -> T { replacement } }",
        ))
        .expect("selected generic dependency trait method values must materialize before indirect execution");
    assert_eq!(outcome.artifact.unwrap().run_text().unwrap(), "linked");
}

#[test]
fn service_executes_aliased_reexported_generic_trait_gats_through_vm_handlers() {
    // The root sees only a public facade alias.  Its selected subtrait method,
    // associated layout GAT, and associated effect-row GAT must nevertheless
    // retain the provider's exact identities through indirect invocation and
    // VM handler dispatch.
    let mut request = request(
        "use bridge::Forward as Capability; use bridge::Audit as Trace; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn worker() -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { let packet = Packet { value: Capability<i64>::relay(0, 41) }; Trace<i64>::note(packet.value) } pub fn apply(callback: () -> i64 / Trace<i64>) -> i64 / Trace<i64> { callback() } pub fn main() -> i64 { handle apply(worker) { Trace<i64>::note(value) with k => k(value + 1) } }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::{Child as Forward, Trace as Audit};".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Item<U> = U; type Effects<U> = {Trace<U>}; fn relay<U>(receiver: i64, value: U) -> U / {Trace<U>} { value } } impl Child<i64> for i64 {}".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("aliased generic trait facade identities must materialize into the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_recursive_module_facade_gat_effect_contracts_through_vm() {
    // `left` declares the parent protocol and exports `right`'s child facade;
    // `right` imports that parent back to define the child and its impls. The
    // module-interface SCC must settle before the root can select a generic
    // associated layout/effect row through the recursive public facade.
    let root = "pub mod left; pub mod right; use left::*; use right::*; pub struct Packet { value: <i64 as Capability<i64>>::Item<i64> } pub fn worker() -> i64 / Trace<i64> { let packet = Packet { value: Capability<i64>::relay<{Trace<i64>}, i64>(0, 41) }; Trace<i64>::note(packet.value) } pub fn main() -> i64 { handle worker() { Trace<i64>::note(value) with k => k(value + 1) } }";
    let left = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<e: EffectRow, U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U>, | e }; } pub use crate::right::Child as Capability;";
    let right = "pub use crate::left::{Parent, Trace}; pub trait Child<T>: Parent<T> {} pub use crate::right::Child as Capability; impl Parent<i64> for i64 { type Item<U> = U; type Effects<U> = {Trace<U>}; fn relay<e: EffectRow, U>(receiver: i64, value: U) -> U / {Trace<U>, | e} { value } } impl Child<i64> for i64 {}";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[("src/left/left.glorious", left), ("src/right/right.glorious", right)],
        ))
        .expect("recursive public module interfaces must converge before VM materialization");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_unselected_recursive_module_facade_gat_effect_contracts() {
    // The same cyclic public interface graph must reach a finite rejected
    // state when no parent implementation supplies the inherited GAT row.
    let root = "pub mod left; pub mod right; use left::*; use right::*; pub fn worker() -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { 0 } pub fn main() -> i64 { worker() }";
    let left = "pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<e: EffectRow, U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U>, | e }; } pub use crate::right::Child as Capability;";
    let right = "pub use crate::left::Parent; pub trait Child<T>: Parent<T> {} pub use crate::right::Child as Capability;";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[("src/left/left.glorious", left), ("src/right/right.glorious", right)],
        ))
    else {
        panic!("a recursive facade manufactured an unselected associated effect row");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4190"),
        "missing bounded recursive-facade evidence rejection: {diagnostics:#?}"
    );
}

#[test]
fn service_executes_recursive_facade_gat_callback_aliases_through_vm() {
    // The callback alias is declared in the reciprocal module, so its generic
    // row projection crosses both the module SCC and alias normalization
    // before a selected trait method becomes an indirect VM callable.
    let root = "pub mod left; pub mod right; use left::*; use right::Callback; pub fn apply(callback: Callback<i64>) -> i64 / Trace<i64> { callback(0, 41) } pub fn main() -> i64 { handle apply(Capability<i64>::relay) { Trace<i64>::note(value) with k => k(value + 1) } }";
    let left = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<e: EffectRow, U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U>, | e }; } pub use crate::right::Child as Capability;";
    let right = "pub use crate::left::{Parent, Trace}; pub trait Child<T>: Parent<T> {} pub use crate::right::Child as Capability; pub type Callback<U> = (i64, U) -> <i64 as Child<i64>>::Item<U> / { <i64 as Child<i64>>::Effects<U> }; impl Parent<i64> for i64 { type Item<U> = i64; type Effects<U> = {Trace<U>}; fn relay<e: EffectRow, U>(receiver: i64, value: U) -> i64 / {Trace<U>, | e} { Trace<U>::note(value) } } impl Child<i64> for i64 {}";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[("src/left/left.glorious", left), ("src/right/right.glorious", right)],
        ))
        .expect("a recursive facade callback alias must materialize into the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_recursive_public_hrtb_callable_aliases_through_vm() {
    // `Callback` crosses the left/right module SCC before reaching the
    // right-side HRTB callable alias. Its row is an inherited GAT projection,
    // so parsing, alias normalization, trait selection, indirect invocation,
    // and handler dispatch all need the same public identities.
    let root = "pub mod left; pub mod right; use left::Callback; use left::Trace; pub fn relay<'a>(value: &'a i64) -> &'a i64 / Trace<i64> { Trace<i64>::note(*value); value } pub fn apply(callback: Callback<i64>) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); *result } pub fn main() -> i64 { handle apply(relay) { Trace<i64>::note(value) with k => k(value + 1) } }";
    let left = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Effects<U>: EffectRow; } pub use crate::right::Child; pub type Callback<U> = crate::right::Inner<U>;";
    let right = "pub use crate::left::{Parent, Trace}; pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Effects<U> = {Trace<U>}; } impl Child<i64> for i64 {} pub type Inner<U> = for<'a> (&'a i64) -> &'a i64 / { <i64 as Child<i64>>::Effects<U> };";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[("src/left/left.glorious", left), ("src/right/right.glorious", right)],
        ))
        .expect("a recursive public HRTB callback alias must reach the VM");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_rejects_recursive_public_hrtb_callable_alias_cycles() {
    let root = "pub mod left; pub mod right; use left::Callback; pub fn apply(callback: Callback<i64>) -> i64 { 0 } pub fn main() -> i64 { 0 }";
    let left = "pub type Callback<U> = crate::right::Inner<U>;";
    let right = "pub type Inner<U> = crate::left::Callback<U>;";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[("src/left/left.glorious", left), ("src/right/right.glorious", right)],
        ))
    else {
        panic!("a mutually recursive public callable alias cycle entered an artifact");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3307"),
        "missing bounded callable-alias-cycle diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn recursive_row_generic_hrtb_callable_aliases_are_order_independent_and_execute() {
    // The type-alias headers themselves carry generic effect rows.  That makes
    // this deliberately exercise the header scanner, public interface
    // convergence through the `left`/`right` SCC, higher-ranked callback
    // normalization, and canonical VM artifact emission in one program.
    let root = "pub mod left; pub mod right; use left::Callback; use left::Trace; pub fn relay<'a>(value: &'a i64) -> &'a i64 / Trace<i64> { Trace<i64>::note(*value); value } pub fn apply(callback: Callback<{Trace<i64>}, i64>) -> i64 / Trace<i64> { let value = 41; let result = callback(&value); *result } pub fn main() -> i64 { handle apply(relay) { Trace<i64>::note(value) with k => k(value + 1) } }";
    let left = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub trait Parent<T> { type Effects<U>: EffectRow; } pub use crate::right::Child; pub type Callback<E: EffectRow, U> = crate::right::Inner<E, U>;";
    let right = "pub use crate::left::{Parent, Trace}; pub trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { type Effects<U> = {Trace<U>}; } impl Child<i64> for i64 {} pub type Inner<E: EffectRow, U> = for<'a> (&'a i64) -> &'a i64 / { <i64 as Child<i64>>::Effects<U>, | E };";
    let sources = [
        ("src/left/left.glorious", left),
        ("src/right/right.glorious", right),
    ];
    let first = StageZeroCompiler::new()
        .compile(request_with_logical_sources(root, &sources))
        .expect("row-generic HRTB aliases must converge through the module SCC");
    let mut reversed = request_with_logical_sources(root, &sources);
    reversed.sources.reverse();
    let second = StageZeroCompiler::new()
        .compile(reversed)
        .expect("source enumeration must not affect row-generic alias interfaces");

    assert!(first.diagnostics.is_empty(), "{:#?}", first.diagnostics);
    assert!(second.diagnostics.is_empty(), "{:#?}", second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 41);
    assert_eq!(second.run_i64().unwrap(), 41);
}

#[test]
fn recursive_public_facade_globs_deduplicate_the_same_callable_alias_identity() {
    // Every imported spelling below ultimately names the provider declaration.
    // A module SCC must therefore not turn identical public aliases into a
    // source-level ambiguity merely because they arrived through multiple
    // facade paths.
    let root = "pub mod provider; pub mod left; pub mod right; use left::*; use right::*; pub fn identity<'a>(value: &'a i64) -> &'a i64 { value } pub fn main() -> i64 { apply(identity) }";
    let provider = "pub type Callback = for<'a> (&'a i64) -> &'a i64; pub fn apply(callback: Callback) -> i64 { let value = 42; let result = callback(&value); *result }";
    let left = "pub use crate::provider::{Callback as Forward, apply}; pub use crate::right::Callback;";
    let right = "pub use crate::provider::Callback; pub use crate::left::{Forward, apply};";
    let sources = [
        ("src/provider/provider.glorious", provider),
        ("src/left/left.glorious", left),
        ("src/right/right.glorious", right),
    ];
    let first = StageZeroCompiler::new()
        .compile(request_with_logical_sources(root, &sources))
        .expect("identical recursive facade aliases must remain one public identity");
    let mut reversed = request_with_logical_sources(root, &sources);
    reversed.sources.reverse();
    let second = StageZeroCompiler::new()
        .compile(reversed)
        .expect("facade identity must not depend on source enumeration");
    assert!(first.diagnostics.is_empty(), "{:#?}", first.diagnostics);
    assert!(second.diagnostics.is_empty(), "{:#?}", second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 42);
    assert_eq!(second.run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_row_generic_recursive_public_callable_alias_cycles() {
    let root = "pub mod left; pub mod right; use left::{Callback, Trace}; pub fn apply(callback: Callback<{Trace<i64>}, i64>) -> i64 { 0 } pub fn main() -> i64 { 0 }";
    let left = "pub effect Trace<T> { [1,1] note(value: T) -> i64; } pub type Callback<E: EffectRow, U> = crate::right::Inner<E, U>;";
    let right = "pub type Inner<E: EffectRow, U> = crate::left::Callback<E, U>;";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[
                ("src/left/left.glorious", left),
                ("src/right/right.glorious", right),
            ],
        ))
    else {
        panic!("a row-generic public callable alias cycle entered an artifact");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3307"),
        "missing bounded row-generic callable-alias-cycle diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_aliased_reexported_generic_trait_gats_without_an_impl() {
    // The implementation-contract normalizer is allowed to reduce only after
    // selection.  A facade alias does not manufacture the missing parent
    // evidence for the same generic associated row.
    let mut request = request(
        "use bridge::Forward as Capability; pub fn worker() -> i64 / { <i64 as Capability<i64>>::Effects<i64> } { 0 } pub fn main() -> i64 { worker() }",
    );
    request.sources.push(SourceInput::new(
        PackageKey("bridge@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub use provider::Child as Forward;".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub trait Parent<T> { type Item<U>; type Effects<U>: EffectRow; fn relay<U>(receiver: T, value: U) -> <Self as Parent<T>>::Item<U> / { <Self as Parent<T>>::Effects<U> }; } pub trait Child<T>: Parent<T> {}".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("a facade alias manufactured generic associated-item evidence");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4190"),
        "missing unselected facade-GAT diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_returns_interprocedural_one_shot_continuation_results_to_the_handler_clause() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn worker() -> i64 / Ask { let value = Ask::ask(); value + 1 } pub fn main() -> i64 { handle worker() { Ask::ask() with k => k(41) + 1 } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("a one-shot continuation result may feed the remainder of its handler clause");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_does_not_treat_a_suspended_handler_as_covering_its_own_clause_effects() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() => Ask::ask() } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("a suspended handler incorrectly discharged its own clause effect")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_follows_dependency_module_declarations_within_their_own_package_world() {
    let mut request = request("use math::api::answer; pub fn main() -> i64 { answer() }");
    let package = PackageKey("math@0.1.0".into());
    request.sources.push(SourceInput::new(
        package.clone(),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub mod api;".as_slice(),
    ));
    request.sources.push(SourceInput::new(
        package,
        LogicalPath::parse("src/api/api.glorious").unwrap(),
        b"pub fn answer() -> i64 { 42 }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .expect("dependency module declarations must claim same-package logical sources");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_keeps_dependency_private_items_outside_the_root_package() {
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::secret; pub fn main() -> i64 { secret() }",
            "math@0.1.0",
            "fn secret() -> i64 { 42 }",
        ))
    else {
        panic!("root package unexpectedly resolved a dependency private item");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| matches!(diagnostic.code, "G3326" | "G4104")),
        "missing cross-package privacy diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_unrooted_dependency_source_packages_instead_of_ignoring_them() {
    let mut request = request("pub fn main() -> i64 { 42 }");
    request.sources.push(SourceInput::new(
        PackageKey("orphan@0.1.0".into()),
        LogicalPath::parse("src/extra/extra.glorious").unwrap(),
        b"pub fn ignored() -> i64 { 0 }".as_slice(),
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("unrooted dependency package source was silently ignored");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3101"),
        "missing dependency package root diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_colliding_dependency_source_module_aliases_before_interface_publication() {
    let mut request = request("use math::answer; pub fn main() -> i64 { answer() }");
    for (package, value) in [("math@0.1.0", "1"), ("math@0.2.0", "2")] {
        request.sources.push(SourceInput::new(
            PackageKey(package.into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            format!("pub fn answer() -> i64 {{ {value} }}").into_bytes(),
        ));
    }
    let error = StageZeroCompiler::new()
        .compile(request)
        .expect_err("colliding dependency aliases must be rejected before resolution");
    let diagnostics = error.diagnostics();
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G7036"),
        "missing deterministic package-alias collision diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_enforces_effect_declaration_visibility_across_package_boundaries() {
    // Effect declarations have the same namespace and authority boundary as
    // other exported semantic declarations.  Exercise both sides through a
    // real perform/handler path so visibility cannot be lost after interface
    // resolution or bypassed by operation lowering.
    let public = StageZeroCompiler::new()
        .compile(request_with_dependency(
            "use math::Signal; pub fn main() -> i64 { handle Signal::ping() { Signal::ping() with k => k(42) } }",
            "math@0.1.0",
            "pub effect Signal { [1,1] ping() -> i64; }",
        ))
        .expect("a public dependency effect must be performable and handleable");
    assert!(public.diagnostics.is_empty(), "{:#?}", public.diagnostics);
    assert_eq!(public.artifact.unwrap().run_i64().unwrap(), 42);

    let private = StageZeroCompiler::new().compile(request_with_dependency(
        "use math::Signal; pub fn main() -> i64 { handle Signal::ping() { Signal::ping() with k => k(42) } }",
        "math@0.1.0",
        "effect Signal { [1,1] ping() -> i64; }",
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = private else {
        panic!("a private dependency effect unexpectedly crossed the package boundary");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| matches!(diagnostic.code, "G3326" | "G4104")),
        "missing cross-package effect-visibility diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_resolves_module_qualified_values_without_last_segment_collisions() {
    let root = "mod math; mod other; pub fn main() -> i64 { math::add(40) + other::add(0) }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(
            root,
            &[
                ("math", "pub fn add(value: i64) -> i64 { value + 2 }"),
                ("other", "pub fn add(value: i64) -> i64 { value }"),
            ],
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_qualified_nominal_identity_across_same_named_modules() {
    // Nominal identity is definition-based, not a final-segment spelling.
    // Two public `Token` declarations must remain distinct through source
    // resolution, record construction/projection, and VM layout selection.
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(
            "pub mod alpha; pub mod beta; pub fn main() -> i64 { let first = alpha::Token { value: 40 }; let second = beta::Token { value: 2 }; first.value + second.value }",
            &[
                ("alpha", "pub struct Token { value: i64 }"),
                ("beta", "pub struct Token { value: i64 }"),
            ],
        ))
        .expect("qualified same-named nominal constructors must remain distinct");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_explicit_import_aliases() {
    let root = "mod math; use math::add_two as add; pub fn main() -> i64 { add(40) }";
    let child = "pub fn add_two(value: i64) -> i64 { value + 2 }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_private_module_import_aliases_from_nested_descendants() {
    let root = "mod api; mod compiler; pub fn main() -> i64 { compiler::frontend::run() }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[
                ("src/api/api.glorious", "pub fn answer() -> i64 { 42 }"),
                (
                    "src/compiler/compiler.glorious",
                    "use crate::api as local; pub mod frontend;",
                ),
                (
                    "src/compiler/frontend/frontend.glorious",
                    "pub fn run() -> i64 { local::answer() }",
                ),
            ],
        ))
        .expect("a nested module must inherit its enclosing private import alias");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_nested_public_reexports_through_private_import_aliases() {
    let root = "pub mod api; pub mod outer; pub fn main() -> i64 { 42 }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/api/api.glorious", "pub fn answer() -> i64 { 42 }"),
            (
                "src/outer/outer.glorious",
                "use crate::api as local; pub mod facade;",
            ),
            ("src/outer/facade/facade.glorious", "pub use local::answer;"),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("private nested import alias unexpectedly entered a public reexport");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "missing public reexport privacy diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_resolves_grouped_import_bindings() {
    let root =
        "mod math; use math::{add_two as add, zero}; pub fn main() -> i64 { add(40) + zero() }";
    let child = "pub fn add_two(value: i64) -> i64 { value + 2 } pub fn zero() -> i64 { 0 }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_glob_imported_values_and_public_nested_reexports() {
    let root = "pub mod math; pub mod facade; use facade::*; pub fn main() -> i64 { add(40) }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[
                (
                    "src/math/math.glorious",
                    "pub mod nested; pub fn ignored() -> i64 { 0 }",
                ),
                (
                    "src/math/nested/nested.glorious",
                    "pub fn add(value: i64) -> i64 { value + 2 }",
                ),
                (
                    "src/facade/facade.glorious",
                    "pub use crate::math::nested::*;",
                ),
            ],
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_ambiguous_glob_imported_values() {
    let root = "mod left; mod right; use left::*; use right::*; pub fn main() -> i64 { answer() }";
    let error = StageZeroCompiler::new().compile(request_with_modules(
        root,
        &[
            ("left", "pub fn answer() -> i64 { 1 }"),
            ("right", "pub fn answer() -> i64 { 2 }"),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("ambiguous glob imports unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4103"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_reports_ambiguous_qualified_module_aliases_as_ambiguity() {
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        "mod left; mod right; mod facade; pub fn main() -> i64 { facade::call() }",
        &[
            ("src/left/left.glorious", "pub mod api;"),
            ("src/right/right.glorious", "pub mod api;"),
            ("src/left/api/api.glorious", "pub fn answer() -> i64 { 1 }"),
            ("src/right/api/api.glorious", "pub fn answer() -> i64 { 2 }"),
            ("src/facade/facade.glorious", "use crate::left::api as client; use crate::right::api as client; pub fn call() -> i64 { client::answer() }"),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("ambiguous qualified module aliases unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4103"),
        "qualified module ambiguity must retain the same source diagnostic as value ambiguity: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_public_reexport_cycles_without_recursing_or_freezing_them() {
    let error = StageZeroCompiler::new().compile(request_with_modules(
        "pub mod alpha; pub mod beta; pub fn main() -> i64 { 42 }",
        &[
            ("alpha", "pub use crate::beta::looped;"),
            ("beta", "pub use crate::alpha::looped;"),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("cyclic public reexports unexpectedly froze as an interface")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "a re-export cycle with no declaration target must fail before body elaboration: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_private_glob_imports_before_body_elaboration() {
    let root = "mod outer; mod facade; pub fn main() -> i64 { 42 }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/outer/outer.glorious", "mod hidden;"),
            (
                "src/outer/hidden/hidden.glorious",
                "pub fn answer() -> i64 { 42 }",
            ),
            ("src/facade/facade.glorious", "use crate::outer::hidden::*;"),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("private glob import unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3326"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_rejects_public_glob_reexports_through_private_modules() {
    let root = "pub mod outer; pub mod facade; pub fn main() -> i64 { 42 }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/outer/outer.glorious", "mod hidden;"),
            (
                "src/outer/hidden/hidden.glorious",
                "pub fn answer() -> i64 { 42 }",
            ),
            (
                "src/facade/facade.glorious",
                "pub use crate::outer::hidden::*;",
            ),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("private public glob reexport unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_resolves_public_import_reexports_from_another_module() {
    let root = "mod math; mod facade; pub fn main() -> i64 { facade::add(40) }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(
            root,
            &[
                ("math", "pub fn add(value: i64) -> i64 { value + 2 }"),
                ("facade", "pub use crate::math::add;"),
            ],
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn private_imports_cannot_be_used_as_module_reexports() {
    let root = "mod math; mod facade; pub fn main() -> i64 { facade::add(40) }";
    let error = StageZeroCompiler::new().compile(request_with_modules(
        root,
        &[
            ("math", "pub fn add(value: i64) -> i64 { value + 2 }"),
            ("facade", "use crate::math::add;"),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("private import unexpectedly acted as a reexport")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4104")
    );
}

#[test]
fn service_rejects_public_members_reached_through_a_private_nested_module() {
    let root = "mod outer; pub fn main() -> i64 { outer::hidden::answer() }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/outer/outer.glorious", "mod hidden;"),
            (
                "src/outer/hidden/hidden.glorious",
                "pub fn answer() -> i64 { 42 }",
            ),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("private nested module unexpectedly leaked its public member")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4104"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_enforces_private_nominal_field_authority_at_source_boundaries() {
    // A private field is usable by the source entry that declared the nominal
    // type, but it must remain opaque to another entry even when the nominal
    // type itself is public.  This exercises the source-to-interface-to-body
    // boundary; header-only tests cannot establish that field authority is
    // retained into construction, projection, and executable lowering.
    let local = "pub struct Secret { private value: i64 } pub fn main() -> i64 { let secret = Secret { value: 42 }; handle secret { Secret { value: found } => found } }";
    let outcome = StageZeroCompiler::new().compile(request(local)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let cross_entry = StageZeroCompiler::new().compile(request_with_logical_sources(
        "pub mod api; use api::Secret; pub fn main() -> i64 { let secret = Secret { value: 42 }; secret.value }",
        &[("src/api/api.glorious", "pub struct Secret { private value: i64 }")],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = cross_entry else {
        panic!("a private nominal field unexpectedly crossed its source authority");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4140"),
        "missing private-field authority diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_cross_module_private_nominal_field_pattern_deconstruction() {
    // Patterns are ownership deconstruction, not a read-only reflection
    // escape hatch. A public nominal shell therefore cannot expose a private
    // field merely by putting the projection in a completion pattern.
    let source = "pub mod api; use api::Secret; pub fn main() -> i64 { let secret = api::make(); handle secret { Secret { value: found } => found } }";
    let result = StageZeroCompiler::new().compile(request_with_logical_sources(
        source,
        &[(
            "src/api/api.glorious",
            "pub struct Secret { private value: i64 } pub fn make() -> Secret { Secret { value: 42 } }",
        )],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = result else {
        panic!("a private nominal field unexpectedly escaped through a pattern");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4218"),
        "missing private-pattern authority diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_cross_module_private_nominal_field_projections_and_assignments() {
    // Obtain the value through the public API so both access forms reach their
    // own Core boundaries instead of being masked by constructor rejection.
    let source = "pub mod api; use api::Secret; pub fn main() -> i64 { let secret = api::make(); secret.value = 7; secret.value }";
    let result = StageZeroCompiler::new().compile(request_with_logical_sources(
        source,
        &[(
            "src/api/api.glorious",
            "pub struct Secret { private value: i64 } pub fn make() -> Secret { Secret { value: 42 } }",
        )],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = result else {
        panic!("a private nominal field unexpectedly allowed direct cross-module access");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4140"),
        "missing private direct-access diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_cross_module_private_enum_payload_pattern_deconstruction() {
    // Named enum payload fields use the same nominal-field grammar and must
    // carry the same authority across enum-layout instantiation.
    let source = "pub mod api; use api::Token; pub fn main() -> i64 { let token = api::make(); handle token { Token::Secret { value: found } => found } }";
    let result = StageZeroCompiler::new().compile(request_with_logical_sources(
        source,
        &[(
            "src/api/api.glorious",
            "pub enum Token { Secret { private value: i64 } } pub fn make() -> Token { Token::Secret { value: 42 } }",
        )],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = result else {
        panic!("a private enum payload unexpectedly escaped through a pattern");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4218"),
        "missing private enum-pattern authority diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_allows_public_nested_module_paths_end_to_end() {
    let root = "mod outer; pub fn main() -> i64 { outer::hidden::answer() }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[
                ("src/outer/outer.glorious", "pub mod hidden;"),
                (
                    "src/outer/hidden/hidden.glorious",
                    "pub fn answer() -> i64 { 42 }",
                ),
            ],
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_public_reexport_of_a_private_nested_module_member() {
    let root = "mod outer; mod facade; pub fn main() -> i64 { facade::answer() }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/outer/outer.glorious", "mod hidden;"),
            (
                "src/outer/hidden/hidden.glorious",
                "pub fn answer() -> i64 { 42 }",
            ),
            (
                "src/facade/facade.glorious",
                "pub use crate::outer::hidden::answer;",
            ),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("public reexport unexpectedly leaked a private nested module member")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4104"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_rejects_exported_private_reexports_even_when_no_body_uses_them() {
    let root = "pub mod outer; pub mod facade; pub fn main() -> i64 { 42 }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/outer/outer.glorious", "mod hidden;"),
            (
                "src/outer/hidden/hidden.glorious",
                "pub fn answer() -> i64 { 42 }",
            ),
            (
                "src/facade/facade.glorious",
                "pub use crate::outer::hidden::answer;",
            ),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("invalid exported reexport unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_compiles_callables_declared_in_inline_modules() {
    let source = "mod math { pub fn add_two(value: i64) -> i64 { value + 2 } } pub fn main() -> i64 { math::add_two(40) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn equivalent_module_source_enumeration_orders_emit_the_same_verified_program() {
    let root = "mod math; mod util; pub fn main() -> i64 { math::add_two(util::forty()) }";
    let modules = [
        ("math", "pub fn add_two(value: i64) -> i64 { value + 2 }"),
        ("util", "pub fn forty() -> i64 { 40 }"),
    ];
    let first = StageZeroCompiler::new()
        .compile(request_with_modules(root, &modules))
        .unwrap();
    let mut reversed = request_with_modules(root, &modules);
    reversed.sources.reverse();
    let second = StageZeroCompiler::new().compile(reversed).unwrap();
    assert_eq!(first.diagnostics, second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_incoherent_impl_heads_before_body_elaboration() {
    let source = r#"
        trait Marker<T> {}
        struct Box<T> {}
        impl<T> Marker<T> for Box<T> {}
        impl Marker<i64> for Box<i64> {}
        pub fn main() -> i64 { 42 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("overlapping implementations unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3404")
    );
}

#[test]
fn service_rejects_references_to_body_locals_in_returned_aggregates() {
    let source = r#"
        pub struct Pair { left: i64, right: i64 }
        pub fn bad() -> (&i64, i64) {
            let pair = Pair { left: 1, right: 2 };
            (&pair.left, pair.right)
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("body-local aggregate reference unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_executes_enum_payload_reference_refinements() {
    let source = r#"
        pub enum Holder { Held(&mut i64), Empty }
        pub fn main() -> i64 {
            let value = 42;
            let holder = Holder::Held(&mut value);
            handle holder is Holder::Held(parent) {
                true => {
                    *parent
                };
                false => 0
            }
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("enum payload reborrows must retain caller provenance through handlers");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let caller_owned = r#"
        pub enum Holder { Held(&mut i64), Empty }
        pub fn relay(value: &mut i64) -> i64 {
            let holder = Holder::Held(value);
            handle holder is Holder::Held(parent) {
                true => {
                    *parent
                };
                false => 0
            }
        }
        pub fn main() -> i64 { 0 }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(caller_owned))
        .expect("caller-owned enum payload reborrows must remain legal");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
}

#[test]
fn service_rejects_body_local_references_in_enum_and_array_effect_payloads() {
    let enum_source = r#"
        pub enum Holder { Held(&i64), Empty }
        effect Store { save(value: Holder); }
        pub fn bad() -> i64 / {Store} {
            let value = 1;
            Store::save(Holder::Held(&value));
            0
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(enum_diagnostics)) =
        StageZeroCompiler::new().compile(request(enum_source))
    else {
        panic!("enum payload borrowing a body local unexpectedly compiled")
    };
    assert!(
        enum_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5015"),
        "missing enum payload suspension diagnostic: {enum_diagnostics:#?}"
    );

    let array_source = r#"
        type Ref = &i64;
        effect Store { save(value: Array<Ref>); }
        pub fn bad() -> i64 / {Store} {
            let value = 1;
            Store::save([&value]);
            0
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(array_diagnostics)) =
        StageZeroCompiler::new().compile(request(array_source))
    else {
        panic!("array payload borrowing a body local unexpectedly compiled")
    };
    assert!(
        array_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5015"),
        "missing array payload suspension diagnostic: {array_diagnostics:#?}"
    );
}

#[test]
fn service_executes_a_borrowed_nominal_projection_through_the_verified_vm() {
    let source = "pub struct Pair { value: i64, other: i64 } pub fn main() -> i64 { let pair = Pair { value: 41, other: 0 }; let value = &pair.value; *value + 1 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_tracks_outlives_through_assigned_tuple_reference_projections() {
    let incoming = StageZeroCompiler::new()
        .compile(request(
            "pub struct Inner { value: &i64 } pub struct Outer { inner: Inner, tag: i64 } pub fn relay(slot: Outer) -> &i64 { slot.inner.value } pub fn main() -> i64 { 0 }",
        ))
        .expect("an incoming aggregate reference must remain returnable");
    assert!(
        incoming.diagnostics.is_empty(),
        "{:#?}",
        incoming.diagnostics
    );

    let local_escape = r#"
        pub struct Inner { value: &i64 }
        pub struct Outer { inner: Inner, tag: i64 }
        pub fn bad(slot: Outer) -> &i64 {
            let value = 1;
            slot.inner.value = &value;
            slot.inner.value
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(local_escape))
    else {
        panic!("body-local aggregate projection unexpectedly escaped")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "missing aggregate projection escape diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_keeps_shared_lifetime_covariance_but_rejects_mutable_nested_coercions() {
    let covariant = r#"
        pub fn accepts_short(value: &i64) -> i64 { 0 }
        pub fn passes_static(value: &'static i64) -> i64 { accepts_short(value) }
        pub fn main() -> i64 { 0 }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(covariant))
        .expect("shared references must remain covariant in their lifetime");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);

    let invariant = r#"
        pub fn accepts_short(slot: &mut &i64) -> i64 { 0 }
        pub fn cannot_shorten(value: &'static i64) -> i64 {
            let long = value;
            accepts_short(&mut long)
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(invariant))
    else {
        panic!("mutable nested reference coercion unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5017"),
        "missing invariant mutable-reference diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_closure_and_effect_payload_lifetime_escapes() {
    let closure = r#"
        pub fn bad() -> () -> &i64 {
            let value = 1;
            let loan = &value;
            () -> &i64 { loan }
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(closure))
    else {
        panic!("closure borrowing a body local unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5014"),
        "{diagnostics:#?}"
    );

    let payload = r#"
        effect Store { save(value: &i64); }
        pub fn bad() -> i64 / {Store} {
            let value = 1;
            Store::save(&value);
            0
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(payload))
    else {
        panic!("effect payload borrowing a body local unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5015"),
        "{diagnostics:#?}"
    );

    let handler = r#"
        effect Tick { tick() -> i64; }
        pub fn bad() -> &i64 / {Tick} {
            let value = 1;
            handle Tick::tick() { Tick::tick() => &value }
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(handler))
    else {
        panic!("handler result borrowing a body local unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_tracks_move_captured_references_through_callables_aggregates_and_effects() {
    let local_callable = r#"
        pub fn main() -> i64 {
            let value = 42;
            let loan = &value;
            let callback = () -> i64 { *move loan };
            callback()
        }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(local_callable))
        .expect("a move-captured reference remains valid while its callable stays local");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let returned_aggregate = r#"
        pub fn bad() -> (() -> &i64, ) {
            let value = 1;
            let loan = &value;
            (() -> &i64 { move loan }, )
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(returned_aggregate))
    else {
        panic!("aggregate containing a moved reference closure unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5014"),
        "{diagnostics:#?}"
    );

    let effect_payload = r#"
        effect Store { save(callback: () -> &i64); }
        pub fn bad() -> i64 / {Store} {
            let value = 1;
            let loan = &value;
            Store::save(() -> &i64 { move loan });
            0
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(effect_payload))
    else {
        panic!("effect payload containing a moved reference closure unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5015"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_reports_outlives_contract_failures_before_vm_lowering() {
    let source = r#"
        pub fn needs_static(value: &'static i64) -> i64 { 0 }
        pub fn bad_return<'a>() -> &'a i64 { let value = 1; &value }
        pub fn main() -> i64 { let value = 1; needs_static(&value) }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("outlives-invalid program unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5017"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_resolves_language_prelude_ownership_traits_by_fixed_identity() {
    let source = r#"
        struct Ticket {}
        impl Use<[0, 1]> for Ticket {}
        impl Drop for Ticket { drop(&mut self) {} }
        pub fn main() -> i64 { 42 }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("the language prelude must provide Use and Drop identities");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn source_trait_named_use_overrides_the_language_prelude_only_when_declared() {
    let source = r#"
        trait Use<T> {}
        struct Ticket {}
        impl Use<i64> for Ticket {}
        pub fn main() -> i64 { 42 }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("a declared local trait must resolve before the language prelude");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_parses_bare_operator_trait_and_implementation_methods() {
    let source = r#"
        struct Number { value: i64 }
        trait Add { +(self: Self, other: Self) -> Self; }
        impl Add for Number {
            +(self: Number, other: Number) -> Number { self }
        }
        pub fn main() -> i64 { 42 }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).expect(
        "operator-named trait and implementation methods must enter one interface contract",
    );
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_selects_and_executes_visible_infix_trait_operators() {
    let source = r#"
        infixl 40 **;
        trait Combine { **(left: i64, right: i64) -> i64; }
        impl Combine for i64 {
            **(left: i64, right: i64) -> i64 { left + right }
        }
        pub fn main() -> i64 { 20 ** 22 }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("a source-defined infix trait operator must lower through selected evidence");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_infers_trait_generic_arguments_for_operator_dispatch() {
    let source = r#"
        infixl 40 **;
        trait Combine<T> { **(left: T, right: T) -> T; }
        impl<T> Combine<T> for T { **(left: T, right: T) -> T { left } }
        pub fn main() -> i64 { 42 ** 0 }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("operator dispatch must infer trait arguments from the receiver");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_selects_prefix_trait_operators_and_preserves_callable_contracts() {
    let source = r#"
        prefix 80 ~;
        trait Invert { ~(value: i64) -> i64; }
        impl Invert for i64 { ~(value: i64) -> i64 { 42 - value } }
        pub fn main() -> i64 { ~1 }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .expect("a source-defined prefix trait operator must execute through the VM");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_trait_operators_accept_heterogeneous_operands_via_method_contracts() {
    let source = r#"
        infixl 40 **;
        trait Choose { **(left: i64, right: Bool) -> i64; }
        impl Choose for i64 { **(left: i64, right: Bool) -> i64 { left } }
        pub fn main() -> i64 { 42 ** true }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).expect(
        "trait operator parameter contracts, not homogeneous primitive rules, govern dispatch",
    );
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_ambiguous_visible_trait_operator_identities() {
    let source = r#"
        infixl 40 **;
        trait First { **(left: i64, right: i64) -> i64; }
        trait Second { **(left: i64, right: i64) -> i64; }
        impl First for i64 { **(left: i64, right: i64) -> i64 { left } }
        impl Second for i64 { **(left: i64, right: i64) -> i64 { right } }
        pub fn main() -> i64 { 1 ** 2 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("ambiguous trait operator unexpectedly entered an artifact");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "G4117" && diagnostic.message.contains("ambiguous")
        }),
        "missing deterministic operator ambiguity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_incompatible_trait_operator_operands_before_mir() {
    let source = r#"
        infixl 40 **;
        trait Combine { **(left: i64, right: i64) -> i64; }
        impl Combine for i64 { **(left: i64, right: i64) -> i64 { left } }
        pub fn main() -> i64 { 1 ** true }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("incompatible trait operator operands unexpectedly entered an artifact");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4107"),
        "missing callable parameter contract diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_selects_operator_traits_imported_into_lexical_scope() {
    let root = r#"
        mod math;
        use math::Combine;
        infixl 40 **;
        pub fn main() -> i64 { 20 ** 22 }
    "#;
    let child = r#"
        pub trait Combine { **(left: i64, right: i64) -> i64; }
        impl Combine for i64 { **(left: i64, right: i64) -> i64 { left + right } }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .expect("an imported public operator trait must be eligible for dispatch");
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_imports_public_fixities_with_their_operator_traits_across_modules() {
    let root = r#"
        pub mod math;
        pub mod facade;
        use facade::*;
        pub fn main() -> i64 { 10 ** 3 ** 2 }
    "#;
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(
            root,
            &[
                (
                    "math",
                    r#"
                        pub infixr 30 **;
                        pub trait Combine { **(left: i64, right: i64) -> i64; }
                        impl Combine for i64 {
                            **(left: i64, right: i64) -> i64 { left - right }
                        }
                    "#,
                ),
                ("facade", "pub use crate::math::*;"),
            ],
        ))
        .expect("a public reexported fixity must group an imported operator trait");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 9);
}

#[test]
fn service_does_not_dispatch_to_operator_traits_outside_lexical_scope() {
    let root = r#"
        mod math;
        infixl 40 **;
        pub fn main() -> i64 { 20 ** 22 }
    "#;
    let child = r#"
        pub trait Combine { **(left: i64, right: i64) -> i64; }
        impl Combine for i64 { **(left: i64, right: i64) -> i64 { left + right } }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request_with_module(root, child))
    else {
        panic!("an out-of-scope operator trait unexpectedly participated in dispatch");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4117"),
        "missing out-of-scope operator diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_forged_operator_implementation_contract_before_dispatch() {
    let source = r#"
        infixl 40 **;
        trait Combine { **(left: i64, right: i64) -> i64; }
        impl Combine for i64 { **(left: i64, right: Bool) -> i64 { left } }
        pub fn main() -> i64 { 20 ** 22 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("a forged operator implementation contract unexpectedly entered an artifact");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4147"),
        "missing frozen trait/implementation contract diagnostic: {diagnostics:#?}"
    );
}
