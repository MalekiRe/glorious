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
fn nominal_boolean_and_enum_fixed_array_patterns_preserve_normalized_identity() {
    accepts("trait Form { type Bit; } impl Form for i64 { type Bit = Bool; } fn choose(bits: [<i64 as Form>::Bit;2]) -> i64 { handle bits { [true,false] => 42, [..] => 0 } } pub fn main() -> i64 { choose([true,false]) }");
    accepts("enum Flag { Off, On } struct Token {} impl Use<[1,1]> for Token {} fn consume(value: Token) -> i64 { let Token {} = value; 42 } fn choose(flags: [Flag;2], value: Token) -> i64 { handle flags { [Flag::On,Flag::On] => consume(value), [Flag::On,Flag::Off] => consume(value), [Flag::Off,..] => consume(value) } } pub fn main() -> i64 { choose([Flag::On,Flag::Off],Token {}) }");
    accepts("enum Bool { False, True } pub fn main() -> i64 { let bits: [Bool;2] = [Bool::True,Bool::False]; handle bits { [Bool::True,Bool::False] => 42, [..] => 0 } }");
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
fn shared_fixed_array_elements_preserve_stored_reference_regions() {
    accepts("fn first<'a>(items: [&'a i64;2]) -> &'a i64 { let [first,..] = items; first } pub fn main() -> i64 { let a = 42; let b = 0; *first([&a,&b]) }");
    accepts("fn first<'a>(items: &[&'a i64;2]) -> &'a i64 { let [first,..] = *items; first } pub fn main() -> i64 { let a = 42; let b = 0; let result = { let items: [&i64;2] = [&a,&b]; first(&items) }; *result }");
    accepts("struct Window<'a> { items: [&'a i64;2], length: usize } fn first<'a>(window: &Window<'a>) -> &'a i64 { let [first,..] = window.items; first } pub fn main() -> i64 { let a = 42; let b = 0; let mut window = Window { items: [&a,&b], length: 2 }; let result = first(&window); window.length = 0; *result }");
    accepts("struct Item<'a> { value: &'a i64 } fn pair<'a>(a: &'a i64, b: &'a i64) -> [Item<'a>;2] { [Item { value: a },Item { value: b }] } pub fn main() -> i64 { let a = 20; let b = 22; let [Item { value: a },Item { value: b }] = pair(&a,&b); *a + *b }");
    accepts("trait View { type Item; } impl View for i64 { type Item = i64; } fn keep<'a>(items: [&'a <i64 as View>::Item;2]) -> [&'a <i64 as View>::Item;2] { items } pub fn main() -> i64 { let a = 20; let b = 22; let [a,b] = keep([&a,&b]); *a + *b }");
}

#[test]
fn unique_fixed_array_elements_preserve_disjoint_mutation_and_reborrows() {
    accepts("fn pair<'a>(a: &'a mut i64, b: &'a mut i64) -> [&'a mut i64;2] { [a,b] } fn bump(items: [&mut i64;2]) { let [a,b] = items; *a = *a + 1; *b = *b + 1; } pub fn main() -> i64 { let mut a = 20; let mut b = 20; bump(pair(&mut a,&mut b)); a+b }");
    accepts("fn bump(value: &mut i64) { *value = *value + 1; } fn update<'a>(items: [&'a mut i64;2]) -> [&'a mut i64;2] { let [a,b] = items; bump(a); bump(b); [a,b] } pub fn main() -> i64 { let mut a = 19; let mut b = 19; let items: [&mut i64;2] = [&mut a,&mut b]; let items = update(update(items)); let [a,b] = items; *a + *b }");
    accepts("fn nested<'a>(a: &'a mut i64, b: &'a mut i64) -> [[&'a mut i64;1];2] { [[a],[b]] } pub fn main() -> i64 { let mut a = 20; let mut b = 20; let [[a],[b]] = nested(&mut a,&mut b); *a = *a + 1; *b = *b + 1; *a + *b }");
    accepts("struct Item<'a> { value: &'a mut i64 } fn keep<T,const N: usize>(items: [T;N]) -> [T;N] { items } pub fn main() -> i64 { let mut a = 20; let mut b = 20; let [Item { value: a },Item { value: b }] = keep([Item { value: &mut a },Item { value: &mut b }]); *a = *a + 1; *b = *b + 1; *a + *b }");
}

#[test]
fn fixed_array_reference_paths_survive_effect_payload_and_resumed_result_boundaries() {
    accepts("effect Relay<'a> { [1,1] relay(items: [&'a i64;2]) -> [&'a i64;2]; } fn relay<'a>(items: [&'a i64;2]) -> [&'a i64;2] { handle Relay<'a>::relay(items) { Relay<'a>::relay(items) => items } } pub fn main() -> i64 { let a = 20; let b = 22; let [a,b] = relay([&a,&b]); *a + *b }");
    accepts("effect Relay<'a> { [1,1] relay(items: [&'a mut i64;2]) -> [&'a mut i64;2]; } fn relay<'a>(items: [&'a mut i64;2]) -> [&'a mut i64;2] { handle Relay<'a>::relay(items) { Relay<'a>::relay(items) => items } } pub fn main() -> i64 { let mut a = 20; let mut b = 20; let [a,b] = relay([&mut a,&mut b]); *a = *a + 1; *b = *b + 1; *a + *b }");
    accepts("fn relay<'a>(items: [&'a mut i64;2]) -> [&'a mut i64;2] { label done { transfer done items } } pub fn main() -> i64 { let mut a = 20; let mut b = 20; let [a,b] = relay([&mut a,&mut b]); *a = *a + 1; *b = *b + 1; *a + *b }");
}

#[test]
fn fixed_array_reference_contracts_preserve_all_possible_inputs_and_reject_escapes() {
    for source in [
        "fn first<'a>(items: [&'a i64;2]) -> &'a i64 { let [first,..] = items; first } pub fn main() -> i64 { let mut a = 41; let b = 0; let result = first([&a,&b]); a = 42; *result }",
        "fn first<'a>(items: [&'a i64;2]) -> &'a i64 { let [first,..] = items; first } pub fn main() -> i64 { let a = 41; let mut b = 0; let result = first([&a,&b]); b = 42; *result }",
        "fn pair<'a>(a: &'a mut i64, b: &'a mut i64) -> [&'a mut i64;2] { [a,b] } pub fn main() -> i64 { let mut a = 42; let unique = &mut a; let items = pair(unique,unique); let [a,b] = items; *a + *b }",
        "fn keep<'a>(items: [&'a i64;2]) -> [&'a i64;2] { items } fn escape<'a>() -> [&'a i64;2] { let local = 42; keep([&local,&local]) } pub fn main() -> i64 { let [a,..] = escape(); *a }",
        "effect Relay<'a> { [1,1] relay(items: [&'a i64;2]) -> [&'a i64;2]; } fn relay<'a>(items: [&'a i64;2]) -> [&'a i64;2] { handle Relay<'a>::relay(items) { Relay<'a>::relay(_) => { let local = 42; [&local,&local] } } } pub fn main() -> i64 { let a = 20; let b = 22; let [a,b] = relay([&a,&b]); *a + *b }",
    ] {
        for optimization in ["0", "2"] {
            let error = StageZeroCompiler::new().compile(request(source, optimization))
                .expect_err("array reference metadata must not grant missing loan authority");
            assert!(error.diagnostics().iter().any(|diagnostic|
                diagnostic.class == grandiose_stage0::DiagnosticClass::Source
                && matches!(diagnostic.code, "G5004" | "G5006" | "G5007" | "G5017" | "G5011" | "G5013")),
                "{source}\n{error:#?}");
        }
    }
}

#[test]
fn const_generic_and_empty_fixed_arrays_keep_bounded_reference_contracts() {
    accepts("fn keep<'a,const N: usize>(items: [&'a i64;N]) -> [&'a i64;N] { items } pub fn main() -> i64 { let a = 20; let b = 22; let [a,b] = keep([&a,&b]); *a + *b }");
    accepts("fn empty<'a>() -> [&'a i64;0] { [] } pub fn main() -> i64 { let [] = empty(); 42 }");
    accepts("fn keep<'a,const N: usize>(items: [&'a i64;N]) -> [&'a i64;N] { items } pub fn main() -> i64 { let items: [&i64;0] = keep([]); let [] = items; 42 }");
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
fn partially_initialized_fixed_arrays_cleanup_only_constructed_elements_on_label_exit() {
    let declarations = "struct Probe<'a> { count: &'a mut i64 } impl<'a> Use<[0,1]> for Probe<'a> {} impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 1; } }";
    for construction in [
        "let items: [Probe<'_>;2] = [Probe { count: &mut count }, transfer done 41];",
        "let items: [[Probe<'_>;1];2] = [[Probe { count: &mut count }], transfer done 41];",
        "let items: [[Probe<'_>;2];1] = [[Probe { count: &mut count }, transfer done 41]];",
    ] {
        accepts(&format!("{declarations} pub fn main() -> i64 {{ let mut count = 0; let result = label done {{ {construction} 0 }}; result + count }}"));
    }
}

#[test]
fn partially_initialized_fixed_arrays_preserve_cleanup_on_effect_resume_and_cancellation() {
    let declarations = "struct Probe<'a> { count: &'a mut i64 } impl<'a> Use<[0,1]> for Probe<'a> {} impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 1; } } effect Stop { [0,1] stop() -> i64; }";
    for (producer, handler) in [
        ("Stop::stop(); Probe { count: count }", "Stop::stop() with _ => 41"),
        ("let item = Probe { count: count }; Stop::stop(); item", "Stop::stop() with _ => 40"),
        ("Stop::stop(); Probe { count: count }", "Stop::stop() => 0"),
    ] {
        accepts(&format!("{declarations} fn next<'a>(count: &'a mut i64) -> Probe<'a> / Stop {{ {producer} }} fn finish(first: &mut i64, second: &mut i64) -> i64 {{ handle {{ let items: [Probe<'_>;2] = [Probe {{ count: first }}, next(second)]; 40 }} {{ {handler} }} }} pub fn main() -> i64 {{ let mut first = 0; let mut second = 0; let result = finish(&mut first, &mut second); result + first + second }}"));
    }
}

#[test]
fn partial_fixed_array_construction_cannot_abandon_initialized_linear_residents() {
    let declarations = "struct Token {} impl Use<[1,1]> for Token {}";
    for body in [
        "pub fn main() -> i64 { label done { let items: [Token;2] = [Token {}, transfer done 42]; let [Token {},Token {}] = items; 42 } }",
        "effect Stop { [0,1] stop() -> i64; } fn next() -> Token / Stop { Stop::stop(); Token {} } pub fn main() -> i64 { handle { let items: [Token;2] = [Token {}, next()]; let [Token {},Token {}] = items; 42 } { Stop::stop() with _ => 42 } }",
    ] {
        for optimization in ["0", "2"] {
            let error = StageZeroCompiler::new().compile(request(&format!("{declarations} {body}"), optimization))
                .expect_err("an initialized linear array element needs an explicit positive use");
            assert!(error.diagnostics().iter().any(|diagnostic|
                diagnostic.class == grandiose_stage0::DiagnosticClass::Source
                    && matches!(diagnostic.code, "G5024" | "G5019")), "{body}\n{error:#?}");
        }
    }
    accepts(&format!("{declarations} pub fn main() -> i64 {{ label done {{ let items: [[Token;0];2] = [[], transfer done 42]; 0 }} }}"));
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
fn callable_raw_storage_preserves_borrowed_capture_identity() {
    let source = r#"use std::*;
        pub fn main() -> i64 {
            let a: i64 = 42;
            let reference = &a;
            let task = () -> i64 { *reference };
            let mut items = Vec::new();
            Vec::push(&mut items, task);
            Vec::reserve(&mut items, 64);
            let mut moved = items;
            let result = handle Vec::pop(&mut moved) {
                Result::Ok(task) => task(), Result::Err(_) => 0
            };
            handle Vec::finish_empty(moved) {
                Result::Ok(_) => result, Result::Err(items) => capture_test_abort(items)
            }
        }
    "#;
    run_callable_storage(source, 42);
}

fn run_callable_storage(source: &str, expected: i64) {
    for optimization in ["0", "2"] {
        let mut request = library_request(source, optimization);
        let library = request.sources.last_mut().unwrap();
        let source = format!("{}\npub fn capture_test_abort<T>(value:T) -> ! {{ __g1_abort() }}", std::str::from_utf8(&library.bytes).unwrap());
        *library = SourceInput::new(library.package.clone(), library.logical_path.clone(), source.as_bytes());
        let compilation = StageZeroCompiler::new().compile(request).unwrap();
        assert!(compilation.diagnostics.is_empty(), "{:?}", compilation.diagnostics);
        let artifact = compilation.artifact.unwrap();
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), expected);
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), expected);
    }
}

#[test]
fn callable_raw_storage_preserves_mutable_capture_between_popped_invocations() {
    run_callable_storage(r#"use std::*;
        pub fn main() -> i64 {
            let mut counter = 40;
            let task = () -> i64 { counter = counter + 1; counter };
            let mut items = Vec::new();
            Vec::push(&mut items, task);
            Vec::reserve(&mut items, 64);
            let result = handle Vec::pop(&mut items) {
                Result::Ok(task) => {
                    let mut stored = move task;
                    let first = (&mut stored)();
                    let second = stored();
                    first + second
                },
                Result::Err(_) => 0
            };
            handle Vec::finish_empty(items) {
                Result::Ok(_) => result, Result::Err(items) => capture_test_abort(items)
            }
        }
    "#, 83);
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
fn library_fixed_array_reference_slots_reborrow_native_residents_without_copying_authority() {
    let source = r#"use std::*;
        pub fn main() -> i64 {
            let mut first = 20;
            let mut second = 20;
            {
                let mut items: [&mut i64;2] = [&mut first,&mut second];
                {
                    let view = array_as_mut_slice(&mut items);
                    handle SliceMut::get(view, 0) {
                        Result::Ok(value) => { *(*value) = *(*value) + 1; },
                        Result::Err(_) => (),
                    };
                };
                {
                    let view = array_as_mut_slice(&mut items);
                    handle SliceMut::get(view, 1) {
                        Result::Ok(value) => { *(*value) = *(*value) + 1; },
                        Result::Err(_) => (),
                    };
                };
            };
            first + second
        }
    "#;
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(library_request(source, optimization))
            .unwrap().artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: trusted array/slice source projects two live reference slots
        // at checked indices and ends the first view before reborrowing.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    }
}

#[test]
fn library_fixed_array_reference_elements_preserve_provenance_through_vec_roundtrip() {
    let source = "use std::*; pub fn main() -> i64 { let a = 20; let b = 22; let items: [&i64;2] = [&a,&b]; let items = array_into_vec(items); let items: [&i64;2] = handle array_try_from_vec(items) { Result::Ok(items) => items, Result::Err(_) => [&a,&b] }; let [a,b] = items; *a + *b }";
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(library_request(source, optimization))
            .unwrap().artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: the library moves initialized reference residents while
        // their caller storage remains alive throughout the roundtrip.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    }
}

#[test]
fn library_fixed_array_reference_vec_does_not_erase_the_source_loan() {
    let source = "use std::*; pub fn main() -> i64 { let mut a: i64 = 41; let items = { let original: [&i64;1] = [&a]; array_into_vec(original) }; a = 42; handle Vec::get(&items,0) { Result::Ok(value) => *(*value), Result::Err(_) => 0 } }";
    for optimization in ["0", "2"] {
        let outcome = StageZeroCompiler::new().compile(library_request(source, optimization));
        assert!(outcome.is_err(), "native owner erased its source loan");
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else { unreachable!() };
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5007"), "{diagnostics:?}");
    }
}

#[test]
fn owning_container_later_insertions_preserve_logical_reference_regions() {
    for source in [
        "use std::*; pub fn main() -> i64 { let a:i64=20; let b:i64=22; let mut items:Vec<&i64> = Vec::new(); { Vec::push(&mut items,&a); Vec::push(&mut items,&b); }; *(*Vec::get_unchecked(&items,0)) + *(*Vec::get_unchecked(&items,1)) }",
        "use std::*; fn insert<'a>(items:&mut Vec<&'a i64>, item:&'a i64) { Vec::push(items,item); } pub fn main() -> i64 { let a:i64=42; let mut items:Vec<&i64> = Vec::new(); insert(&mut items,&a); *(*Vec::get_unchecked(&items,0)) }",
        "use std::*; pub fn main() -> i64 { let mut a:i64=42; let mut items:Vec<&i64> = Vec::new(); handle true { true => Vec::push(&mut items,&a), false => { a=41; } }; *(*Vec::get_unchecked(&items,0)) }",
        "use std::*; pub fn main() -> i64 { let mut a:i64=41; { let mut items:Vec<&mut i64> = Vec::new(); Vec::push(&mut items,&mut a); handle Vec::pop(&mut items) { Result::Ok(value) => { *value = *value + 1; }, Result::Err(_) => () }; }; a }",
        "use std::*; pub fn main() -> i64 { let a:i64=20; let b:i64=22; let mut items:Vec<(&i64,&i64)> = Vec::new(); Vec::push(&mut items,(&a,&b)); let pair = Vec::get_unchecked(&items,0); *pair.0 + *pair.1 }",
        "use std::*; pub fn main() -> i64 { let a:i64=42; let mut inner:Vec<&i64> = Vec::new(); Vec::push(&mut inner,&a); let mut outer:Vec<Vec<&i64>> = Vec::new(); Vec::push(&mut outer,inner); let inner = Vec::get_unchecked(&outer,0); *(*Vec::get_unchecked(inner,0)) }",
    ] {
        for optimization in ["0", "2"] {
            let artifact = StageZeroCompiler::new().compile(library_request(source, optimization))
                .unwrap_or_else(|error| panic!("{source}: {error:?}")).artifact.unwrap();
            let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
            // SAFETY: every source referent remains alive through owner use.
            assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
            assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        }
    }
    for source in [
        "use std::*; pub fn main() -> i64 { let mut a:i64=41; let mut items:Vec<&i64> = Vec::new(); { Vec::push(&mut items,&a); }; a=42; *(*Vec::get_unchecked(&items,0)) }",
        "use std::*; pub fn main() -> i64 { let mut items:Vec<&i64> = Vec::new(); { let a:i64=42; Vec::push(&mut items,&a); }; *(*Vec::get_unchecked(&items,0)) }",
        "use std::*; fn bad<'a>(items:&mut Vec<&'a i64>) { let a:i64=42; Vec::push(items,&a); } pub fn main() -> i64 { 42 }",
        "use std::*; pub fn main() -> i64 { let mut a:i64=41; let mut items:Vec<&i64> = Vec::new(); handle true { true => Vec::push(&mut items,&a), false => () }; a=42; *(*Vec::get_unchecked(&items,0)) }",
        "use std::*; pub fn main() -> i64 { let mut a:i64=41; let mut items:Vec<&mut i64> = Vec::new(); Vec::push(&mut items,&mut a); a=42; handle Vec::pop(&mut items) { Result::Ok(value) => *value, Result::Err(_) => 0 } }",
        "use std::*; pub fn main() -> i64 { let a:i64=20; let mut b:i64=21; let mut items:Vec<(&i64,&i64)> = Vec::new(); { Vec::push(&mut items,(&a,&b)); }; b=22; let pair = Vec::get_unchecked(&items,0); *pair.0 + *pair.1 }",
    ] {
        for optimization in ["0", "2"] {
            let outcome = StageZeroCompiler::new().compile(library_request(source, optimization));
            let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else { panic!("owner lost an inserted reference: {source}"); };
            assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G5007" | "G5013" | "G5017" | "G5022")), "{source}: {diagnostics:?}");
        }
    }
}

#[test]
fn generic_owner_conversions_preserve_regions_shared_across_type_arguments() {
    let declarations = "use std::*; trait Convert<T> { fn convert(value:Self) -> T; } impl<'a> Convert<Vec<&'a i64>> for &'a i64 { fn convert(value:Self) -> Vec<&'a i64> { let mut items:Vec<&'a i64> = Vec::new(); Vec::push(&mut items,value); items } } fn convert<T,U>(value:U) -> T where U:Convert<T> { Convert<T>::convert(value) } ";
    let source = format!("{declarations} pub fn main() -> i64 {{ let a:i64=42; let items:Vec<&i64> = convert(&a); *(*Vec::get_unchecked(&items,0)) }}");
    let rejected = format!("{declarations} pub fn main() -> i64 {{ let mut a:i64=41; let items:Vec<&i64> = {{ let value = &a; convert(value) }}; a=42; *(*Vec::get_unchecked(&items,0)) }}");
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(library_request(&source, optimization))
            .unwrap_or_else(|error| panic!("{source}: {error:?}")).artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: the shared resident keeps its caller storage alive.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        let outcome = StageZeroCompiler::new().compile(library_request(&rejected, optimization));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else { panic!("generic conversion erased a resident region"); };
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5007"), "{diagnostics:?}");
    }
}

fn shared_slot_request(source: &str, optimization: &str) -> CompilationRequest {
    let mut request = library_request(source, optimization);
    // This ordinary source-defined, Copy-only interior-mutable slot is a
    // different owner representation from Vec, with no compiler-recognized
    // spelling. Its allocation intentionally lives until the program ends.
    let support = r#"
        pub fn capture_test_abort<T>(value:T) -> ! { __g1_abort() }
        pub struct SharedSlot<T> { private pointer:*mut Option<T>, private marker:PhantomData<T> }
        impl<T> SharedSlot<T> where T:Use<[0,*]> {
            pub fn new() -> Self {
                let raw = unsafe { __g1_memory_allocate(size_of<Option<T>>(),align_of<Option<T>>()) };
                handle unsafe { __g1_memory_is_null(raw) } != 0 { true => __g1_abort(), false => () };
                let pointer = unsafe { __g1_memory_cast<u8,Option<T>>(raw) };
                unsafe { __g1_memory_write(pointer,None); };
                SharedSlot { pointer:pointer, marker:PhantomData {} }
            }
            pub fn copy(value:&Self) -> Self { SharedSlot { pointer:value.pointer, marker:PhantomData {} } }
            pub fn set(value:&Self, item:T) {
                let previous = unsafe { __g1_memory_read(__g1_memory_as_const(value.pointer)) };
                discard(previous);
                unsafe { __g1_memory_write(value.pointer,Some(item)); }
            }
            pub fn get(value:&Self) -> Option<T> {
                let item = unsafe { __g1_memory_read(__g1_memory_as_const(value.pointer)) };
                unsafe { __g1_memory_write(value.pointer,item); };
                item
            }
        }
        pub struct AnchoredSlot<'a,T> { private anchor:&'a i64, private pointer:*mut Option<T> }
        impl<'a,T> AnchoredSlot<'a,T> where T:Use<[0,*]> {
            pub fn new(anchor:&'a i64) -> Self {
                let raw = unsafe { __g1_memory_allocate(size_of<Option<T>>(),align_of<Option<T>>()) };
                handle unsafe { __g1_memory_is_null(raw) } != 0 { true => __g1_abort(), false => () };
                let pointer = unsafe { __g1_memory_cast<u8,Option<T>>(raw) };
                unsafe { __g1_memory_write(pointer,None); };
                AnchoredSlot { anchor:anchor, pointer:pointer }
            }
            pub fn set(value:&Self, item:T) {
                let previous = unsafe { __g1_memory_read(__g1_memory_as_const(value.pointer)) };
                discard(previous);
                unsafe { __g1_memory_write(value.pointer,Some(item)); }
            }
            pub fn get(value:&Self) -> Option<T> {
                let item = unsafe { __g1_memory_read(__g1_memory_as_const(value.pointer)) };
                unsafe { __g1_memory_write(value.pointer,item); };
                item
            }
        }
        pub struct RegionSlot<'a> { private anchor:&'a i64, private pointer:*mut Option<&'a i64> }
        impl<'a> RegionSlot<'a> {
            pub fn new(anchor:&'a i64) -> Self {
                let slot:SharedSlot<&'a i64> = SharedSlot::new();
                RegionSlot { anchor:anchor, pointer:slot.pointer }
            }
            pub fn set(value:&Self, item:&'a i64) {
                let slot = SharedSlot { pointer:value.pointer, marker:PhantomData {} };
                SharedSlot::set(&slot,item);
            }
            pub fn get(value:&Self) -> Option<&'a i64> {
                let slot = SharedSlot { pointer:value.pointer, marker:PhantomData {} };
                SharedSlot::get(&slot)
            }
        }
    "#;
    let index = request.sources.iter().position(|source| source.package == PackageKey("std@0.1.0".into())).unwrap();
    let mut bytes = request.sources[index].bytes.to_vec();
    bytes.extend_from_slice(support.as_bytes());
    request.sources[index] = SourceInput::new(PackageKey("std@0.1.0".into()), LogicalPath::parse("src/lib.glorious").unwrap(), bytes);
    request
}

#[test]
fn physical_owner_fields_do_not_hide_distinct_logical_residents_with_the_same_lifetime() {
    for (name, ty) in [("AnchoredSlot", "AnchoredSlot<'_,&i64>"), ("RegionSlot", "RegionSlot<'_>")] {
        let source = format!("use std::*; pub fn main() -> i64 {{ let a:i64=20; let b:i64=42; let slot:{ty} = {name}::new(&a); {name}::set(&slot,&b); handle {name}::get(&slot) {{ Result::Ok(value) => *value, Result::Err(_) => 0 }} }}");
        let rejected = format!("use std::*; pub fn main() -> i64 {{ let a:i64=20; let mut b:i64=41; let slot:{ty} = {name}::new(&a); {{ {name}::set(&slot,&b); }}; b=42; handle {name}::get(&slot) {{ Result::Ok(value) => *value, Result::Err(_) => 0 }} }}");
        for optimization in ["0", "2"] {
            let artifact = StageZeroCompiler::new().compile(shared_slot_request(&source, optimization))
                .unwrap_or_else(|error| panic!("{source}: {error:?}")).artifact.unwrap();
            let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
            // SAFETY: both the physical anchor and the raw-backed shared resident
            // remain alive while the source-defined owner is used.
            assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
            assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
            let outcome = StageZeroCompiler::new().compile(shared_slot_request(&rejected, optimization));
            let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else { panic!("physical field hid the later logical resident"); };
            assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5007"), "{diagnostics:?}");
        }
    }
}

#[test]
fn empty_cloned_interior_mutable_owners_keep_later_region_updates() {
    let source = "use std::*; pub fn main() -> i64 { let a:i64=42; let slot:SharedSlot<&i64> = { let original:SharedSlot<&i64> = SharedSlot::new(); SharedSlot::copy(&original) }; { let alias = SharedSlot::copy(&slot); SharedSlot::set(&alias,&a); }; handle SharedSlot::get(&slot) { Result::Ok(value) => *value, Result::Err(_) => 0 } }";
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(shared_slot_request(source, optimization))
            .unwrap().artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: the source-defined owner only copies shared-reference
        // residents, and the referent outlives both aliases of its allocation.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    }
    for source in [
        "use std::*; pub fn main() -> i64 { let mut a:i64=41; let slot:SharedSlot<&i64> = SharedSlot::new(); { let alias = SharedSlot::copy(&slot); SharedSlot::set(&alias,&a); }; a=42; handle SharedSlot::get(&slot) { Result::Ok(value) => *value, Result::Err(_) => 0 } }",
        "use std::*; pub fn main() -> i64 { let slot:SharedSlot<&i64> = SharedSlot::new(); { let a:i64=42; let alias = SharedSlot::copy(&slot); SharedSlot::set(&alias,&a); }; handle SharedSlot::get(&slot) { Result::Ok(value) => *value, Result::Err(_) => 0 } }",
        "use std::*; fn bad<'a>(slot:&SharedSlot<&'a i64>) { let a:i64=42; SharedSlot::set(slot,&a); } pub fn main() -> i64 { 42 }",
    ] {
        for optimization in ["0", "2"] {
            let outcome = StageZeroCompiler::new().compile(shared_slot_request(source, optimization));
            let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else { panic!("shared owner lost a later store: {source}"); };
            assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G5007" | "G5013" | "G5017" | "G5022")), "{source}: {diagnostics:?}");
        }
    }
}

#[test]
fn logical_capture_probe_owning_container_keeps_borrowed_callable_environment() {
    for source in [
        "use std::*; fn bad() -> Vec<() -> i64> { let a:i64=42; let reference = &a; let task = () -> i64 { *reference }; let mut items:Vec<() -> i64> = Vec::new(); Vec::push(&mut items,task); items } pub fn main() -> i64 { 42 }",
        "use std::*; pub fn main() -> i64 { let mut a:i64=41; let mut items:Vec<() -> i64> = Vec::new(); { let reference = &a; let task = () -> i64 { *reference }; Vec::push(&mut items,task); }; a=42; handle Vec::pop(&mut items) { Result::Ok(task) => task(), Result::Err(_) => 0 } }",
        "use std::*; struct Holder { task:() -> i64 } fn bad() -> Vec<Holder> { let a:i64=42; let reference = &a; let task = () -> i64 { *reference }; let mut items:Vec<Holder> = Vec::new(); Vec::push(&mut items,Holder { task:task }); items } pub fn main() -> i64 { 42 }",
        "use std::*; fn factory<'a>(reference:&'a i64) -> () -> i64 { () -> i64 { *reference } } fn bad() -> Vec<() -> i64> { let a:i64=42; let mut items:Vec<() -> i64> = Vec::new(); Vec::push(&mut items,factory(&a)); items } pub fn main() -> i64 { 42 }",
    ] {
        for optimization in ["0", "2"] {
            let outcome = StageZeroCompiler::new().compile(library_request(source, optimization));
            let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else { panic!("owning container erased callable captures: {source}"); };
            assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G5007" | "G5013" | "G5014" | "G5017" | "G5022")), "{source}: {diagnostics:?}");
        }
    }
}

#[test]
fn logical_capture_probe_invocation_updates_an_empty_captured_owner() {
    let source = "use std::*; pub fn main() -> i64 { let mut a:i64=41; let slot:SharedSlot<&i64> = SharedSlot::new(); { let alias = SharedSlot::copy(&slot); let task = () -> () { SharedSlot::set(&alias,&a); }; task(); }; a=42; handle SharedSlot::get(&slot) { Result::Ok(value) => *value, Result::Err(_) => 0 } }";
    for optimization in ["0", "2"] {
        let outcome = StageZeroCompiler::new().compile(shared_slot_request(source, optimization));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else { panic!("callable invocation lost an inserted reference"); };
        assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G5007" | "G5013" | "G5017" | "G5022")), "{diagnostics:?}");
    }
}

#[test]
fn logical_capture_probe_live_residents_and_expired_owners_validate() {
    for (source, execute) in [
        ("use std::*; pub fn main() -> i64 { let a:i64=42; let reference = &a; let task = () -> i64 { *reference }; let mut items = Vec::new(); Vec::push(&mut items,task); let result = handle Vec::pop(&mut items) { Result::Ok(task) => task(), Result::Err(_) => 0 }; handle Vec::finish_empty(items) { Result::Ok(_) => result, Result::Err(items) => capture_test_abort(items) } }", false),
        ("use std::*; pub fn main() -> i64 { let mut a:i64=41; { let reference = &a; let task = () -> i64 { *reference }; let mut items = Vec::new(); Vec::push(&mut items,task); let result = handle Vec::pop(&mut items) { Result::Ok(task) => task(), Result::Err(_) => 0 }; handle Vec::finish_empty(items) { Result::Ok(_) => result, Result::Err(items) => capture_test_abort(items) }; }; a=42; a }", false),
        ("use std::*; pub fn main() -> i64 { let a:i64=42; let slot:SharedSlot<&i64> = SharedSlot::new(); { let alias = SharedSlot::copy(&slot); let task = () -> () { SharedSlot::set(&alias,&a); }; task(); }; handle SharedSlot::get(&slot) { Result::Ok(value) => *value, Result::Err(_) => 0 } }", true),
        ("use std::*; fn factory<'a>(reference:&'a i64) -> () -> i64 { move (reference) { *reference } } pub fn main() -> i64 { let a:i64=42; let mut items:Vec<() -> i64> = Vec::new(); Vec::push(&mut items,factory(&a)); let result = handle Vec::pop(&mut items) { Result::Ok(task) => task(), Result::Err(_) => 0 }; handle Vec::finish_empty(items) { Result::Ok(_) => result, Result::Err(items) => capture_test_abort(items) } }", true),
    ] {
        for optimization in ["0", "2"] {
            let artifact = StageZeroCompiler::new().compile(shared_slot_request(source, optimization))
                .unwrap_or_else(|error| panic!("{source}: {error:?}")).artifact.unwrap();
            let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
            // The original local Vec probes check formation and decoding;
            // the slot and owned factory capture also execute. The separate
            // raw-storage test below executes a borrowed local capture.
            if execute {
                // SAFETY: the slot's shared reference outlives both aliases.
                assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
                assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
            }
        }
    }
}

#[test]
fn callable_container_cannot_hide_a_factory_local_capture_slot() {
    // Preserve the original factory source: its reference handle belongs to
    // the factory frame even though the referenced integer lives in main.
    let source = "use std::*; fn factory<'a>(reference:&'a i64) -> () -> i64 { () -> i64 { *reference } } pub fn main() -> i64 { let a:i64=42; let mut items:Vec<() -> i64> = Vec::new(); Vec::push(&mut items,factory(&a)); let result = handle Vec::pop(&mut items) { Result::Ok(task) => task(), Result::Err(_) => 0 }; handle Vec::finish_empty(items) { Result::Ok(_) => result, Result::Err(items) => capture_test_abort(items) } }";
    for optimization in ["0", "2"] {
        let error = match StageZeroCompiler::new().compile(shared_slot_request(source, optimization)) {
            Err(error) => error,
            Ok(_) => panic!("container storage cannot extend the factory capture slot's lifetime"),
        };
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5014"),
            "O{optimization}: {:#?}", error.diagnostics());
    }
}

#[test]
fn native_callable_owner_storage_executes() {
    let source = "use std::*; pub fn main() -> i64 { let a:i64=42; let reference = &a; let task = () -> i64 { *reference }; let mut items = Vec::new(); Vec::push(&mut items,task); let result = handle Vec::pop(&mut items) { Result::Ok(task) => task(), Result::Err(_) => 0 }; handle Vec::finish_empty(items) { Result::Ok(_) => result, Result::Err(items) => capture_test_abort(items) } }";
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(shared_slot_request(source, optimization)).unwrap().artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: every callback is invoked while the captured source lives.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
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
fn independent_verifier_rejects_duplicating_a_unique_fixed_array_element() {
    use grandiose_stage0::{VmInstruction, VmType};
    let artifact = StageZeroCompiler::new().compile(request(
        "fn pair<'a>(a: &'a mut i64, b: &'a mut i64) -> [&'a mut i64;2] { [a,b] } pub fn main() -> i64 { let mut a = 20; let mut b = 22; let [a,b] = pair(&mut a,&mut b); *a + *b }", "0",
    )).unwrap().artifact.unwrap();
    let candidate = grandiose_stage0::decode_program(&artifact.canonical_bytes()).unwrap();
    let mut duplicate = candidate.clone();
    let fields = duplicate.functions.values_mut().find_map(|function|
        function.instructions.iter_mut().find_map(|instruction| match instruction {
            VmInstruction::MakeArrayOwned { fields, element_type: VmType::Reference { unique: true, .. }, .. }
                if fields.len() == 2 => Some(fields),
            _ => None,
        })).expect("owned unique-reference array constructor");
    fields[1] = fields[0];
    rejects_candidate(duplicate);
    let mut copied = candidate;
    let constructor = copied.functions.values_mut().find_map(|function|
        function.instructions.iter_mut().find(|instruction| matches!(instruction,
            VmInstruction::MakeArrayOwned { element_type: VmType::Reference { unique: true, .. }, .. })))
        .expect("owned unique-reference array constructor");
    let VmInstruction::MakeArrayOwned { dst, fields, element_type } = constructor.clone() else { unreachable!() };
    *constructor = VmInstruction::MakeArray { dst, fields, element_type };
    rejects_candidate(copied);
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
