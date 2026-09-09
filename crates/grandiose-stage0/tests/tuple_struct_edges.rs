use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};

fn compile(source: &str) -> Result<grandiose_stage0::CompilationOutcome, grandiose_stage0::ServiceError> {
    let package = PackageKey("tuple-struct-edges@1".into());
    StageZeroCompiler::new().compile(CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"tuple-struct-edges")),
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
fn transparent_aliases_preserve_constructor_and_pattern_identity() {
    run("struct Pair<T>(T,i64); type IntPair = Pair<i64>;
        pub fn main() -> i64 { let IntPair(first, second) = IntPair(40,2); first + second }", 42);
    run("struct Pair<A,B>(A,B); type Flipped<A,B> = Pair<B,A>;
        pub fn main() -> i64 { let Flipped<i64,()>(first, second) = Flipped<i64,()>((),42); let () = first; second }", 42);
    run("struct Pair<A,B>(A,B); type Flipped<A,B> = Pair<B,A>;
        pub fn main() -> i64 { let Flipped(first, second) = Pair((),42); let () = first; second }", 42);
}

#[test]
fn higher_ranked_constructor_callbacks_preserve_borrowed_fields() {
    run("struct View<'a>(&'a i64);
        fn apply(make: for<'a> (&'a i64) -> View<'a>) -> i64 {
            let value = 42; let view = make(&value); *view.0
        }
        pub fn main() -> i64 { apply(View) }", 42);
    for constructor in ["View<'static>", "StaticView"] {
        let source = format!("struct View<'a>(&'a i64); struct StaticView(&'static i64);
            fn apply(make: for<'a> (&'a i64) -> View<'a>) -> i64 {{ 42 }}
            pub fn main() -> i64 {{ apply({constructor}) }}");
        let error = compile(&source).unwrap_err();
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.class == grandiose_stage0::DiagnosticClass::Source), "{error:?}");
    }
}

#[test]
fn ordinary_values_win_over_same_spelling_type_aliases() {
    run("struct Pair(i64); type Make = Pair; fn Make(value: i64) -> i64 { value + 2 }
        pub fn main() -> i64 { Make(40) }", 42);
    run("struct Pair(i64); pub fn main() -> i64 {
        let Pair = fn(value: i64) -> i64 { value + 2 }; Pair(40)
    }", 42);
}

#[test]
fn canonical_anonymous_functions_keep_explicit_unit_and_effect_contracts() {
    run("pub fn main() -> i64 { let do_nothing = fn() {}; do_nothing();
        (fn(value: i64) -> i64 { value + 2 })(40) }", 42);
    run("pub fn main() -> i64 { let mut value = 40;
        let change = fn() { value = value + 2; }; change(); value }", 42);
    run("effect Read { value() -> i64; } pub fn main() -> i64 {
        let read = fn() -> i64 / {Read} { Read::value() };
        handle read() { Read::value() => 42 }
    }", 42);
    for source in [
        "pub fn main() -> i64 { let invalid = fn() { 42 }; 42 }",
        "pub fn main() -> i64 { let invalid = fn(value) -> i64 { value }; 42 }",
        "pub fn main() -> i64 { let invalid = fn() -> {}; 42 }",
    ] { assert!(compile(source).is_err(), "{source}"); }
}

#[test]
fn tuple_struct_destructors_and_partial_moves_follow_owned_fields() {
    run("struct Probe<'a>(&'a mut i64);
        impl<'a> Use<[0,1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.0 = *self.0 + 1; } }
        struct Pair<'a>(Probe<'a>,i64);
        pub fn main() -> i64 { let mut count = 0; let result = {
            let pair = Pair(Probe(&mut count),41); let number = move pair.1; number
        }; count + result }", 42);
    for body in ["move pair.0", "let Pair(first, second) = pair; first + second"] {
        let source = format!("struct Pair(i64,i64); impl Drop for Pair {{ drop(&mut self) -> {{}} }}
            pub fn main() -> i64 {{ let pair = Pair(40,2); {body} }}");
        let error = compile(&source).unwrap_err();
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.message.to_lowercase().contains("drop")), "{error:?}");
    }
}

#[test]
fn nominal_constructor_constants_follow_context_and_remain_independent() {
    run("struct Tag<n: u32>();
        fn first() -> Tag<7> { Tag() } fn second() -> Tag<9> { Tag() }
        pub fn main() -> i64 { let a = first(); let b = second();
            let Tag<7>() = a; let Tag<9>() = b; 42 }", 42);
    run("struct Tag<n: u32> {} fn make() -> Tag<7> { Tag {} }
        pub fn main() -> i64 { make(); 42 }", 42);
    run("enum Tag<n: u32> { Value(i64) } fn make() -> Tag<7> { Tag::Value(42) }
        pub fn main() -> i64 { handle make() { Tag::Value(value) => value } }", 42);
    run("struct Tag<n: u32 = 7>(); pub fn main() -> i64 { let Tag<7>() = Tag(); 42 }", 42);
    assert!(compile("struct Tag<n: u32>(); pub fn main() -> i64 { let value = Tag(); 42 }").is_err());
    assert!(compile("struct Tag<n: u32>(); fn make() -> Tag<7> { Tag<9>() } pub fn main() -> i64 { 42 }").is_err());
}

#[test]
fn nominal_constructor_rows_follow_payloads_and_expected_results() {
    run("effect Read { value() -> i64; } struct Task<e: EffectRow>(() -> i64 / {|e});
        fn read() -> i64 / {Read} { Read::value() }
        pub fn main() -> i64 { let task = Task(read); let Task(callback) = task;
            handle callback() { Read::value() => 42 } }", 42);
    run("effect Read { value() -> i64; } struct Token<e: EffectRow>();
        fn make() -> Token<{Read}> { Token() }
        pub fn main() -> i64 { let Token<{Read}>() = make(); 42 }", 42);
    let error = compile("struct Token<e: EffectRow>(); pub fn main() -> i64 { Token(); 42 }").unwrap_err();
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.class == grandiose_stage0::DiagnosticClass::Source), "{error:?}");
    assert!(compile("effect Read { value() -> i64; } struct Task<e: EffectRow>(() -> i64 / {|e});
        fn read() -> i64 / {Read} { Read::value() }
        pub fn main() -> i64 { let task = Task<{}>(read); 42 }").is_err());
}

#[test]
fn nominal_effect_row_defaults_are_declaration_scoped() {
    run("struct Token<e: EffectRow = {}>(); pub fn main() -> i64 { let Token<{}>() = Token(); 42 }", 42);
    run("mod declaration {
            pub effect Read { value() -> i64; }
            pub struct Token<e: EffectRow = {Read}>();
        }
        effect Read { value() -> i64; }
        pub fn main() -> i64 {
            let declaration::Token<{declaration::Read}>() = declaration::Token(); 42
        }", 42);
}

#[test]
fn nominal_defaults_substitute_earlier_arguments_of_each_kind() {
    run("struct Pair<T, U = T>(T, U);
        pub fn main() -> i64 { let Pair(left, right) = Pair<i64>(20, 22); left + right }", 42);
    run("struct Token<e: EffectRow, f: EffectRow = e>();
        pub fn main() -> i64 { let Token<{}, {}>() = Token<{}>(); 42 }", 42);
    run("struct View<'a, 'b = 'a>();
        pub fn main() -> i64 { let View<'static, 'static>() = View<'static>(); 42 }", 42);
    run("struct Box<T>(T); type DefaultBox<T = i64> = Box<T>;
        pub fn main() -> i64 { let value: DefaultBox = Box(42); value.0 }", 42);
    run("struct Box<T>(T); type DefaultBox<T = i64> = Box<T>;
        pub fn main() -> i64 { let DefaultBox<i64>(value) = DefaultBox(42); value }", 42);
    run("struct Node<T = Node<()>>();
        pub fn main() -> i64 { let Node<Node<()>>() = Node(); 42 }", 42);
    run("mod declaration { pub struct Value(pub i64); pub struct Box<T = Value>(pub T); }
        struct Value();
        pub fn main() -> i64 { let value: declaration::Box = declaration::Box(declaration::Value(42)); value.0.0 }", 42);
}

#[test]
fn unused_nominal_defaults_reject_forward_self_and_wrong_kind_references() {
    for declaration in [
        "struct Bad<T = T>();",
        "struct Bad<T = U, U = i64>();",
        "struct Bad<e: EffectRow = f, f: EffectRow = {}>();",
        "struct Bad<'a = 'b, 'b = 'static>();",
        "struct Bad<n: u32 = m, m: u32 = 1>();",
        "struct Bad<n: u32 = m * 0, m: u32 = 1>();",
        "struct Tag<n: u32>(); struct Bad<T = Tag<n * 0>, n: u32 = 1>();",
        "struct Bad<T = i64, e: EffectRow = T>();",
        "struct Bad<e: EffectRow = {}, T = e>();",
        "struct Bad<T = Bad>();",
        "struct Bad<T = Other>(); struct Other<T = Bad>();",
    ] {
        assert!(compile(&format!("{declaration} pub fn main() -> i64 {{ 42 }}")).is_err(),
            "invalid unused default compiled: {declaration}");
    }
}

#[test]
fn acyclic_generic_default_expansion_has_a_total_resource_bound() {
    let mut source = String::from("struct Layer0<T = ()>();");
    for index in 1..=14 {
        let earlier = index - 1;
        source.push_str(&format!(
            "struct Layer{index}<T = (Layer{earlier}, Layer{earlier})>();",
        ));
    }
    source.push_str("pub fn main() -> i64 { 42 }");
    let error = compile(&source).expect_err("exponential defaults must stop at a resource diagnostic");
    assert!(error.diagnostics().iter().any(|diagnostic|
        diagnostic.code == "G3318" && diagnostic.message.contains("resource limit")),
        "missing default-expansion resource diagnostic: {error:?}");
}
