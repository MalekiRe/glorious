use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};
use std::collections::BTreeMap;

fn request(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("fixed-array-cases@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"fixed-array-cases")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), optimization.into())]),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn accepts(source: &str) {
    for optimization in ["0", "2"] {
        let result = StageZeroCompiler::new()
            .compile(request(source, optimization))
            .unwrap();
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let artifact = result.artifact.unwrap();
        assert_eq!(
            artifact
                .run_i64()
                .unwrap_or_else(|error| panic!("{source}: {error:?}")),
            42
        );
        assert_eq!(
            decode_and_verify_program(&artifact.canonical_bytes())
                .unwrap()
                .run_i64()
                .unwrap(),
            42
        );
    }
}

fn rejects(source: &str) {
    for optimization in ["0", "2"] {
        assert!(
            StageZeroCompiler::new()
                .compile(request(source, optimization))
                .is_err(),
            "{source}"
        );
    }
}

#[test]
fn fixed_array_literals_patterns_and_const_inference_execute() {
    accepts(
        "fn keep<T,const N: usize>(value: [T;N]) -> [T;N] { value } pub fn main() -> i64 { let [a,b]: [i64;2] = keep([20,22]); a + b }",
    );
    accepts("fn make() -> [i64;2] { [20,22] } pub fn main() -> i64 { let [a,b] = make(); a+b }");
    accepts(
        "fn empty(value: [i64;0]) -> i64 { let [] = value; 42 } pub fn main() -> i64 { empty([]) }",
    );
}

#[test]
fn fixed_array_length_is_part_of_type_identity() {
    rejects("fn bad(value: [i64;2]) -> [i64;3] { value } pub fn main() -> i64 { 42 }");
    rejects("pub fn main() -> i64 { let x: [i64;2] = [1,2,3]; 42 }");
    rejects("fn bad<const N:u32>(value: [i64;N]) -> i64 { 42 } pub fn main() -> i64 { 42 }");
    rejects("fn bad(value: [i64;-1]) -> i64 { 42 } pub fn main() -> i64 { 42 }");
}

#[test]
fn nested_array_products_and_contextual_element_widths_execute() {
    accepts(
        "fn make() -> [[u8;2];2] { [[10,11],[20,22]] } pub fn main() -> i64 { let [[_,_],[a,b]] = make(); handle a == 20 { true => handle b == 22 { true => 42, false => 0 }, false => 0 } }",
    );
    accepts(
        "type Pair<T> = [T;1+1]; fn make() -> Pair<i64> { [20,22] } pub fn main() -> i64 { let [a,b] = make(); a+b }",
    );
    accepts(
        "trait Width { const Value: usize; } impl Width for i64 { const Value = 2; } fn make() -> [i64;<i64 as Width>::Value] { [20,22] } pub fn main() -> i64 { let [a,b]: [i64;<i64 as Width>::Value] = make(); a+b }",
    );
    rejects("fn make() -> [u8;2] { [256,0] } pub fn main() -> i64 { 42 }");
    rejects("struct Infinite { nested: [Infinite;1] } pub fn main() -> i64 { 42 }");
}

#[test]
fn borrowed_fixed_array_patterns_observe_empty_variants_without_moving_shells() {
    let declarations = "struct Probe<'a> { count: &'a mut i64 } impl<'a> Use<[0,1]> for Probe<'a> {} impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 1; } } enum State<'a> { Full(Probe<'a>), Empty } struct Slot<'a> { states: [State<'a>;2] } ";
    for reference in ["&'a Slot<'b>", "&'a mut Slot<'b>"] {
        let argument = if reference.contains("mut") { "&mut slot" } else { "&slot" };
        accepts(&format!("{declarations} fn inspect<'a,'b>(slot: {reference}) -> i64 {{ handle slot.states {{ [State::Full(_), State::Empty] => 41, _ => 0 }} }} pub fn main() -> i64 {{ let mut count = 0; let observed = {{ let mut slot = Slot {{ states: [State::Full(Probe {{ count: &mut count }}), State::Empty] }}; inspect({argument}) }}; observed + count }}"));
        let source = format!("{declarations} fn consume(value: Probe) -> i64 {{ 42 }} fn inspect<'a,'b>(slot: {reference}) -> i64 {{ handle slot.states {{ [State::Full(item), State::Empty] => consume(item), _ => 0 }} }} pub fn main() -> i64 {{ 42 }}");
        for optimization in ["0", "2"] {
            let error = StageZeroCompiler::new().compile(request(&source, optimization)).expect_err("a borrowed array pattern cannot transfer its resident destructor");
            assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.class == grandiose_stage0::DiagnosticClass::Source && matches!(diagnostic.code, "G5004" | "G4141")), "{source}\n{error:#?}");
        }
    }
}

#[test]
fn sparse_array_remainders_preserve_prefix_and_suffix() {
    accepts("pub fn main() -> i64 { let [a,..,b]: [i64;4] = [20,1,2,22]; a+b }");
    accepts("pub fn main() -> i64 { let [..,a,b]: [i64;4] = [1,2,20,22]; a+b }");
    accepts("pub fn main() -> i64 { let [a,b,..]: [i64;4] = [20,22,1,2]; a+b }");
    accepts("pub fn main() -> i64 { let [..]: [i64;0] = []; 42 }");
    accepts(
        "pub fn main() -> i64 { let values: [i64;3] = [1,0,1]; handle values { [1,..,1] => 42, [..] => 0 } }",
    );
    rejects("pub fn main() -> i64 { let [a,..,b]: [i64;1] = [42]; a+b }");
    rejects("pub fn main() -> i64 { let [..,..]: [i64;2] = [20,22]; 42 }");
}

#[test]
fn fixed_arrays_preserve_zero_sized_linear_obligations_and_partial_cleanup() {
    let token = "struct Token {} impl Use<[1,1]> for Token {} ";
    accepts(&format!(
        "{token} pub fn main() -> i64 {{ let empty: [Token;0] = []; 42 }}"
    ));
    accepts(&format!(
        "{token} pub fn main() -> i64 {{ let [a,b]: [Token;2] = [Token {{}},Token {{}}]; let Token {{}} = a; let Token {{}} = b; 42 }}"
    ));
    rejects(&format!(
        "{token} pub fn main() -> i64 {{ let [a,..]: [Token;2] = [Token {{}},Token {{}}]; let Token {{}} = a; 42 }}"
    ));
    accepts(
        "struct Probe<'a> { count: &'a mut i64 } impl<'a> Use<[0,1]> for Probe<'a> {} impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 1; } } pub fn main() -> i64 { let mut a = 20; let mut b = 20; { let [first,..]: [Probe<'_>;2] = [Probe { count: &mut a },Probe { count: &mut b }]; () }; a+b }",
    );
}

#[test]
fn unused_named_linear_fixed_array_is_rejected() {
    rejects(
        "struct Token {} impl Use<[1,1]> for Token {} pub fn main() -> i64 { let values: [Token;2] = [Token {},Token {}]; 42 }",
    );
}

/// These are the exact four non-callback helper declarations from the library.
/// The complete array module additionally requires universal RunsIn callback
/// evidence, tracked separately; do not change its production bounds here.
fn library_request(source: &str, optimization: &str) -> CompilationRequest {
    let mut request = request(source, optimization);
    let mut library = grandiose_stage0::service::STANDARD_LIBRARY_FRAGMENTS
        .iter()
        .filter(|(path, _)| {
            matches!(
                *path,
                "src/lib.glorious" | "src/foundation.glorious" | "src/memory.glorious"
            )
        })
        .map(|(_, source)| *source)
        .collect::<Vec<_>>()
        .join("\n");
    let array = include_str!("../../../stdlib/src/array.glorious");
    library.push_str(array.split("fn array_fill_from").next().unwrap());
    // An intentionally partial source profile must bind its machine leaves
    // explicitly; it must not pass the bundled-library byte-identity gate.
    request.runtime_manifest = Some(grandiose_stage0::RuntimeManifestInput {
        standard_library: PackageKey("std@0.1.0".into()),
        host_imports: vec![],
        selectors: library
            .lines()
            .filter(|line| line.ends_with(';'))
            .filter_map(|line| {
                if !line.starts_with("__g1_") && !line.starts_with("unsafe fn __g1_") {
                    return None;
                }
                let start = line.find("__g1_")?;
                let name = line[start..]
                    .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                    .next()?;
                let role = grandiose_stage0::PrimitiveRole::parse_selector_name(
                    name.strip_prefix("__g1_")?.replace('_', "-"),
                )?;
                Some(grandiose_stage0::PrimitiveSelector {
                    role,
                    module_path: "crate".into(),
                    name: name.into(),
                })
            })
            .collect(),
    });
    request.sources.push(SourceInput::new(
        PackageKey("std@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        library.as_bytes(),
    ));
    request
}

#[test]
fn library_array_storage_and_conversion_preserve_owners() {
    let source = r#"use std::*;
        pub fn main() -> i64 {
            let mut items: [i64;2] = [20,21];
            let first = {
                let view = array_as_slice(&items);
                handle Slice::get(view, 0) { Result::Ok(value) => *value, Result::Err(_) => 0 }
            };
            {
                let view = array_as_mut_slice(&mut items);
                handle SliceMut::get(view, 1) { Result::Ok(value) => { *value = 22; }, Result::Err(_) => () };
            };
            let values = array_into_vec(items);
            let values = handle array_try_from_vec<i64,3>(values) { Result::Err(values) => values, Result::Ok(_) => Vec::new() };
            let array: [i64;2] = handle array_try_from_vec(values) { Result::Ok(array) => array, Result::Err(_) => [0,0] };
            let [_,second] = array;
            first + second
        }
    "#;
    for optimization in ["0", "2"] {
        let request = library_request(source, optimization);
        let result = StageZeroCompiler::new()
            .compile(request.clone())
            .unwrap_or_else(|error| {
                if let grandiose_stage0::ServiceError::Failed(diagnostics) = &error {
                    for diagnostic in diagnostics {
                        let excerpt = diagnostic.primary.and_then(|span| {
                            request
                                .sources
                                .iter()
                                .find(|source| source.key == span.file)
                                .map(|source| {
                                    String::from_utf8_lossy(
                                        &source.bytes[span.start.saturating_sub(30) as usize
                                            ..(span.end as usize + 30).min(source.bytes.len())],
                                    )
                                    .into_owned()
                                })
                        });
                        eprintln!("{} {} {:?}", diagnostic.code, diagnostic.message, excerpt);
                    }
                }
                panic!("library array compilation failed")
            });
        let artifact = result.artifact.unwrap();
        // SAFETY: locally compiled source uses the library's raw-memory contract.
        assert_eq!(
            unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(),
            42
        );
        let program = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        assert_eq!(
            unsafe { program.run_i64_with_unsafe(Default::default()) }.unwrap(),
            42
        );
    }
}

#[test]
fn library_array_conversion_steps() {
    for (name, source) in [
        (
            "into",
            "use std::*; pub fn main() -> i64 { let a: [i64;2] = [20,22]; let v = array_into_vec(a); as<i64>(Vec::len(&v)) + 40 }",
        ),
        (
            "mismatch",
            "use std::*; pub fn main() -> i64 { let a: [i64;2] = [20,22]; let v = array_into_vec(a); handle array_try_from_vec<i64,3>(v) { Result::Err(v) => as<i64>(Vec::len(&v)) + 40, Result::Ok(_) => 0 } }",
        ),
        (
            "match",
            "use std::*; pub fn main() -> i64 { let a: [i64;2] = [20,22]; let v = array_into_vec(a); let a: [i64;2] = handle array_try_from_vec(v) { Result::Ok(a) => a, Result::Err(_) => [0,0] }; let [a,b] = a; a+b }",
        ),
    ] {
        let artifact = StageZeroCompiler::new()
            .compile(library_request(source, "0"))
            .unwrap()
            .artifact
            .unwrap();
        assert_eq!(
            unsafe { artifact.run_i64_with_unsafe(Default::default()) }
                .unwrap_or_else(|error| panic!("{name}: {error:?}")),
            42
        );
    }
}

fn rejects_candidate(mut candidate: grandiose_stage0::CandidateVmProgram) {
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = grandiose_stage0::encode_program(&candidate);
    assert!(grandiose_stage0::verify_vm_program(candidate).is_err());
    assert!(decode_and_verify_program(&bytes).is_err());
}

#[test]
fn independent_verifier_rejects_forged_fixed_array_shapes() {
    use grandiose_stage0::{VmInstruction as I, VmPattern, VmType, pattern::ArrayPatternRest};
    let artifact = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let [a,b]: [i64;2] = [20,22]; a+b }",
            "0",
        ))
        .unwrap()
        .artifact
        .unwrap();
    let candidate = grandiose_stage0::decode_program(&artifact.canonical_bytes()).unwrap();
    let mut arity = candidate.clone();
    let function = arity.functions.get_mut(&arity.entry).unwrap();
    let fields = function
        .instructions
        .iter_mut()
        .find_map(|instruction| match instruction {
            I::MakeArrayOwned { fields, .. } | I::MakeArray { fields, .. } => Some(fields),
            _ => None,
        })
        .expect("array constructor");
    fields.pop();
    rejects_candidate(arity);
    let mut projection = candidate.clone();
    let function = projection.functions.get_mut(&projection.entry).unwrap();
    function.parameters = 1;
    function.registers = vec![
        VmType::FixedArray {
            element: Box::new(VmType::I64),
            length: 2,
        },
        VmType::I64,
    ];
    function.instructions = vec![
        I::ProjectArray {
            dst: 1,
            base: 0,
            index: 2,
            field_count: 2,
            element_type: VmType::I64,
        },
        I::Return { value: 1 },
    ];
    rejects_candidate(projection);
    let mut identity = candidate.clone();
    let function = identity.functions.get_mut(&identity.entry).unwrap();
    let length = function
        .registers
        .iter_mut()
        .find_map(|ty| match ty {
            VmType::FixedArray { length, .. } => Some(length),
            _ => None,
        })
        .expect("fixed array register");
    *length = 3;
    rejects_candidate(identity);
    let mut pattern = candidate.clone();
    let function = pattern.functions.get_mut(&pattern.entry).unwrap();
    function.registers = vec![
        VmType::I64,
        VmType::FixedArray {
            element: Box::new(VmType::I64),
            length: 3,
        },
        VmType::Bool,
        VmType::I64,
    ];
    function.instructions = vec![
        I::ConstI64 { dst: 0, value: 1 },
        I::MakeArray {
            dst: 1,
            fields: vec![0, 0, 0],
            element_type: VmType::I64,
        },
        I::PatternTest {
            dst: 2,
            subject: 1,
            pattern: VmPattern::Array {
                element: VmType::I64,
                elements: vec![VmPattern::Any, VmPattern::Any],
                rest: Some(ArrayPatternRest {
                    prefix: 1,
                    omitted: 1,
                }),
            },
        },
        I::ConstI64 { dst: 3, value: 42 },
        I::Return { value: 3 },
    ];
    pattern.fingerprint = pattern.computed_fingerprint();
    grandiose_stage0::verify_vm_program(pattern.clone()).unwrap();
    decode_and_verify_program(&grandiose_stage0::encode_program(&pattern)).unwrap();
    for malformed in [
        ArrayPatternRest {
            prefix: 3,
            omitted: 1,
        },
        ArrayPatternRest {
            prefix: 1,
            omitted: 0,
        },
        ArrayPatternRest {
            prefix: 1,
            omitted: u32::MAX,
        },
    ] {
        let mut forged = pattern.clone();
        let function = forged.functions.get_mut(&forged.entry).unwrap();
        let I::PatternTest {
            pattern: VmPattern::Array { rest, .. },
            ..
        } = &mut function.instructions[2]
        else {
            unreachable!()
        };
        *rest = Some(malformed);
        rejects_candidate(forged);
    }
    let mut overflow = candidate.clone();
    let function = overflow.functions.get_mut(&overflow.entry).unwrap();
    function.parameters = 1;
    function.registers = vec![
        VmType::FixedArray {
            element: Box::new(VmType::U128),
            length: u64::MAX,
        },
        VmType::I64,
    ];
    function.instructions = vec![I::ConstI64 { dst: 1, value: 42 }, I::Return { value: 1 }];
    rejects_candidate(overflow);
    let mut resizing = candidate;
    let mut function = resizing.functions[&resizing.entry].clone();
    function.parameters = 2;
    function.registers = vec![
        VmType::Reference {
            unique: true,
            referent: Box::new(VmType::FixedArray {
                element: Box::new(VmType::I64),
                length: 2,
            }),
        },
        VmType::I64,
        VmType::I64,
    ];
    function.instructions = vec![
        I::ArrayPushMove {
            value: 0,
            item: 1,
            element_type: VmType::I64,
        },
        I::ConstI64 { dst: 2, value: 42 },
        I::Return { value: 2 },
    ];
    resizing.functions = BTreeMap::from([(resizing.entry, function)]);
    rejects_candidate(resizing);
}
