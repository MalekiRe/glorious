use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    ast::{
        Associativity, EffectDecl, EffectRowSyntax, EnumDecl, FieldVisibility, FixityDecl,
        FixityKind, Function, GenericParamKind, GenericParams, StructDecl, TypeAliasDecl,
        TypeSyntax, TypeSyntaxKind, Visibility,
    },
    source_bundle::{Segment, SourceBundle},
    CompileOptions, LlvmOptions, OptimizationLevel,
};
use grandiose_vm::{verify, SystemHost, Value, Vm};

const NESTED_GENERIC_NOMINAL_FIELDS: &str = r#"
    struct NestedSlot<T> { value: T }
    struct Ring<T> { slots: Vec<NestedSlot<T>> }
    struct ArrayRing<T> { slots: Array<NestedSlot<T>> }

    impl<T> Use<[0,1]> for NestedSlot<T> where T: Use<[0,1]> {}
    impl<T> Use<[0,1]> for Ring<T> where Vec<NestedSlot<T>>: Use<[0,1]> {}
    impl<T> Use<[0,1]> for ArrayRing<T> where Array<NestedSlot<T>>: Use<[0,1]> {}

    empty_ring<T>() -> Ring<T> { Ring { slots: Vec::new() } }
    forward_ring(value: Ring<i64>) -> Ring<i64> { value }
    wrap_array<T>(slots: Array<NestedSlot<T>>) -> ArrayRing<T> {
        ArrayRing { slots: move slots }
    }
    forward_array(value: Array<NestedSlot<i64>>) -> ArrayRing<i64> {
        wrap_array(move value)
    }
    answer() -> usize {
        let ring = forward_ring(empty_ring());
        Vec::len(&ring.slots)
    }
    main() -> () { () }
"#;

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
}

fn self_host_bundle() -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary = Segment::new(
        root.join("main.glorious").to_string_lossy(),
        "mod frontend;\nmod probe;\n\nmain() { run_compiler_host(probe::headers::interface_application) }\n",
    );
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("probe/probe.glorious"),
        root.join("probe/headers/headers.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let mut source = fs::read_to_string(&path)
                .unwrap()
                .replace("pub mod lossless;\n", "")
                .replace("pub mod bodies;\n", "")
                .replace("pub mod resolution;\n", "")
                .replace("pub mod elaboration;\n", "");
            if path.ends_with("probe/probe.glorious") {
                source = source
                    .replace("pub mod lexer;\n", "")
                    .replace("pub mod scanner;\n", "");
            }
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

fn push_u32(output: &mut Vec<u8>, value: u32) {
    output.extend(value.to_le_bytes());
}

fn push_u64(output: &mut Vec<u8>, value: u64) {
    output.extend(value.to_le_bytes());
}

fn push_bytes(output: &mut Vec<u8>, value: &[u8]) {
    push_u32(output, value.len().try_into().unwrap());
    output.extend(value);
}

fn push_string(output: &mut Vec<u8>, value: &str) {
    push_bytes(output, value.as_bytes());
}

fn encode_optional_lifetime(output: &mut Vec<u8>, lifetime: Option<&str>) {
    match lifetime {
        Some(lifetime) => {
            output.push(1);
            push_string(output, lifetime);
        }
        None => output.push(0),
    }
}

fn encode_type(
    output: &mut Vec<u8>,
    program: &grandiose::ast::Program,
    ty: &TypeSyntax,
) -> Result<(), ()> {
    if program.fixed_array(ty.span).is_some() || !program.type_const_arguments(ty.span).is_empty() {
        return Err(());
    }
    match &ty.kind {
        TypeSyntaxKind::Path(segments) => {
            output.push(1);
            push_u32(output, segments.len().try_into().unwrap());
            for segment in segments {
                push_string(output, &segment.name);
            }
        }
        TypeSyntaxKind::SharedReference { lifetime, referent } => {
            output.push(2);
            encode_optional_lifetime(output, lifetime.as_ref().map(|value| value.name.as_str()));
            encode_type(output, program, referent)?;
        }
        TypeSyntaxKind::UniqueReference { lifetime, referent } => {
            output.push(3);
            encode_optional_lifetime(output, lifetime.as_ref().map(|value| value.name.as_str()));
            encode_type(output, program, referent)?;
        }
        TypeSyntaxKind::Tuple(elements) => {
            output.push(4);
            push_u32(output, elements.len().try_into().unwrap());
            for element in elements {
                encode_type(output, program, element)?;
            }
        }
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            lifetime_arguments,
        } => {
            output.push(5);
            encode_type(output, program, constructor)?;
            push_u32(output, lifetime_arguments.len().try_into().unwrap());
            for lifetime in lifetime_arguments {
                push_string(output, &lifetime.lifetime.name);
            }
            push_u32(output, arguments.len().try_into().unwrap());
            for argument in arguments {
                encode_type(output, program, argument)?;
            }
        }
        TypeSyntaxKind::Never => output.push(6),
        TypeSyntaxKind::Projection { .. } => return Err(()),
    }
    Ok(())
}

fn encode_generics(output: &mut Vec<u8>, generics: Option<&GenericParams>) -> Result<(), ()> {
    let parameters = generics.map_or(&[][..], |generics| generics.params.as_slice());
    push_u32(output, parameters.len().try_into().unwrap());
    for parameter in parameters {
        let kind = match parameter.kind {
            GenericParamKind::Type => 1,
            GenericParamKind::Lifetime => 2,
            GenericParamKind::EffectRow => 3,
            GenericParamKind::Const(_) => 4,
        };
        output.push(kind);
        push_string(output, &parameter.name);
        if parameter.const_default.is_some() {
            return Err(());
        }
    }
    Ok(())
}

fn encode_effect_row(
    output: &mut Vec<u8>,
    program: &grandiose::ast::Program,
    row: &EffectRowSyntax,
) -> Result<(), ()> {
    push_u32(output, row.effects.len().try_into().unwrap());
    for effect in &row.effects {
        encode_type(output, program, effect)?;
    }
    match &row.tail {
        Some(tail) => {
            output.push(1);
            push_string(output, &tail.name);
        }
        None => output.push(0),
    }
    Ok(())
}

fn encode_common(
    output: &mut Vec<u8>,
    program: &grandiose::ast::Program,
    span: grandiose::span::Span,
    name: &str,
    generics: Option<&GenericParams>,
) -> Result<(), ()> {
    output.push(u8::from(program.visibility(span) == Visibility::Public));
    push_string(output, name);
    encode_generics(output, generics)
}

fn encode_alias(
    output: &mut Vec<u8>,
    program: &grandiose::ast::Program,
    declaration: &TypeAliasDecl,
) -> Result<(), ()> {
    encode_common(
        output,
        program,
        declaration.span,
        &declaration.name,
        declaration.generics.as_ref(),
    )?;
    encode_type(output, program, &declaration.target)
}

fn encode_struct(
    output: &mut Vec<u8>,
    program: &grandiose::ast::Program,
    declaration: &StructDecl,
) -> Result<(), ()> {
    encode_common(
        output,
        program,
        declaration.span,
        &declaration.name,
        declaration.generics.as_ref(),
    )?;
    push_u32(output, declaration.fields.len().try_into().unwrap());
    for field in &declaration.fields {
        output.push(u8::from(field.visibility == FieldVisibility::Public));
        push_string(output, &field.name);
        encode_type(output, program, &field.ty)?;
    }
    Ok(())
}

fn encode_enum(
    output: &mut Vec<u8>,
    program: &grandiose::ast::Program,
    declaration: &EnumDecl,
) -> Result<(), ()> {
    encode_common(
        output,
        program,
        declaration.span,
        &declaration.name,
        declaration.generics.as_ref(),
    )?;
    push_u32(output, declaration.variants.len().try_into().unwrap());
    for variant in &declaration.variants {
        push_string(output, &variant.name);
        push_u32(output, variant.fields.len().try_into().unwrap());
        for field in &variant.fields {
            encode_type(output, program, field)?;
        }
    }
    Ok(())
}

fn encode_callable(
    output: &mut Vec<u8>,
    program: &grandiose::ast::Program,
    declaration: &Function,
) -> Result<(), ()> {
    if declaration.where_clause.is_some() {
        return Err(());
    }
    encode_common(
        output,
        program,
        declaration.span,
        &declaration.name,
        declaration.generics.as_ref(),
    )?;
    push_u32(output, declaration.params.len().try_into().unwrap());
    for parameter in &declaration.params {
        push_string(output, &parameter.name);
        encode_type(output, program, &parameter.ty)?;
    }
    match &declaration.return_type {
        Some(return_type) => {
            output.push(1);
            encode_type(output, program, return_type)?;
        }
        None => output.push(0),
    }
    match &declaration.outward_effects {
        Some(effects) => {
            output.push(1);
            encode_effect_row(output, program, effects)?;
        }
        None => output.push(0),
    }
    Ok(())
}

fn encode_fixity(
    output: &mut Vec<u8>,
    program: &grandiose::ast::Program,
    declaration: &FixityDecl,
) {
    output.push(u8::from(
        program.visibility(declaration.span) == Visibility::Public,
    ));
    output.push(match declaration.kind {
        FixityKind::Prefix => 1,
        FixityKind::Infix(Associativity::Left) => 2,
        FixityKind::Infix(Associativity::Right) => 3,
        FixityKind::Infix(Associativity::None) => 4,
    });
    output.push(declaration.precedence);
    push_string(output, &declaration.name);
}

fn encode_effect(
    output: &mut Vec<u8>,
    program: &grandiose::ast::Program,
    declaration: &EffectDecl,
) -> Result<(), ()> {
    encode_common(
        output,
        program,
        declaration.span,
        &declaration.name,
        declaration.generics.as_ref(),
    )?;
    output.push(u8::from(declaration.where_clause.is_some()));
    push_u32(output, declaration.operations.len().try_into().unwrap());
    for operation in &declaration.operations {
        push_string(output, &operation.name);
        encode_generics(output, operation.generics.as_ref())?;
        push_u32(output, operation.params.len().try_into().unwrap());
        for parameter in &operation.params {
            push_string(output, &parameter.name);
            encode_type(output, program, &parameter.ty)?;
        }
        match &operation.return_type {
            Some(result) => {
                output.push(1);
                encode_type(output, program, result)?;
            }
            None => output.push(0),
        }
        output.push(u8::from(operation.terminal));
        push_u64(output, operation.resumption_lower.try_into().unwrap());
        match operation.resumption_upper {
            Some(upper) => {
                output.push(1);
                push_u64(output, upper.try_into().unwrap());
            }
            None => output.push(0),
        }
        output.push(u8::from(operation.has_resumption_quantity));
        output.push(u8::from(operation.where_clause.is_some()));
    }
    Ok(())
}

enum Interface<'a> {
    Alias(&'a TypeAliasDecl),
    Fixity(&'a FixityDecl),
    Struct(&'a StructDecl),
    Enum(&'a EnumDecl),
    Effect(&'a EffectDecl),
    Function(&'a Function),
}

impl Interface<'_> {
    fn start(&self) -> usize {
        match self {
            Self::Alias(declaration) => declaration.span.start,
            Self::Fixity(declaration) => declaration.span.start,
            Self::Struct(declaration) => declaration.span.start,
            Self::Enum(declaration) => declaration.span.start,
            Self::Effect(declaration) => declaration.span.start,
            Self::Function(declaration) => declaration.span.start,
        }
    }

    fn encode(self, output: &mut Vec<u8>, program: &grandiose::ast::Program) -> Result<(), ()> {
        match self {
            Self::Alias(declaration) => {
                output.push(3);
                encode_alias(output, program, declaration)
            }
            Self::Fixity(declaration) => {
                output.push(6);
                encode_fixity(output, program, declaration);
                Ok(())
            }
            Self::Struct(declaration) => {
                output.push(8);
                encode_struct(output, program, declaration)
            }
            Self::Enum(declaration) => {
                output.push(9);
                encode_enum(output, program, declaration)
            }
            Self::Effect(declaration) => {
                output.push(7);
                encode_effect(output, program, declaration)
            }
            Self::Function(declaration) => {
                output.push(12);
                encode_callable(output, program, declaration)
            }
        }
    }
}

fn encode_rust_interfaces(output: &mut Vec<u8>, source: &str) {
    let Ok(tokens) = grandiose::lexer::lex(source) else {
        output.push(1);
        return;
    };
    let Ok(program) = grandiose::parser::parse(tokens) else {
        output.push(3);
        return;
    };
    let mut declarations = program
        .type_aliases
        .iter()
        .map(Interface::Alias)
        .chain(program.fixities.iter().map(Interface::Fixity))
        .chain(program.structs.iter().map(Interface::Struct))
        .chain(program.enums.iter().map(Interface::Enum))
        .chain(program.effects.iter().map(Interface::Effect))
        .chain(program.functions.iter().map(Interface::Function))
        .collect::<Vec<_>>();
    declarations.sort_by_key(Interface::start);

    let mut encoded = Vec::new();
    push_u32(&mut encoded, declarations.len().try_into().unwrap());
    for declaration in declarations {
        if declaration.encode(&mut encoded, &program).is_err() {
            output.push(3);
            return;
        }
    }
    output.push(0);
    output.extend(encoded);
}

fn corpus(directory: &Path) -> Vec<PathBuf> {
    let valid = [
        "",
        "type Word = u32; struct Empty {} enum Void {}",
        "pub type Pair<T, U> = core::Pair<T, U>; pub struct Wrap<'a, T, E: EffectRow> { private value: &'a T, marker: Phantom<T> } pub enum Maybe<T> { None, Some(T) }",
        "struct Visibility { plain: u8, private hidden: String; private: Bool private private: i64 }",
        "enum Shape<T> { Unit, Empty(), One(T,), Pair(T, T); Nested(core::Result<T, !>) }",
        "type Grouped = (u8); type Singleton = (u8,); struct Tuples { grouped: (u8), singleton: (u8,) }",
        "type Before<T> = Vec<T>; struct Middle<T> { value: Before<T> } call<T>(value: Middle<T>) -> T { unreachable() } enum After<T> { None, Some(T) }",
        "mod outer { type Local = u8; struct Boxed<T> { private value: T } mod inner { enum Nested<T> { Empty, Value(T) } } inside(value: Local) { () } } type After = ();",
        "struct Separators { first: u8,; second: u16 third: u32; } enum VariantSeparators { A,; B C; }",
        "type Commented<T,> = Vec</* element */ T,>; struct CommentBox<T,> { /* before */ private value: Commented<T>, } enum CommentMaybe<T,> { None, Some(/* payload */ T,), }",
        "read<T, E: EffectRow>(value: T) -> Result<T, !> / {Console, Io<T> | E} { value }",
        "invoke<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }",
        "trait Marker<T> where T: Bound {}",
        "trait Read { read(self: &Self) -> i64; } struct Item { value: i64 } impl Read for Item { read(self: &Item) -> i64 { self.value } }",
        "mod outer { pub type A = u8; pub struct S { private x: u8 } pub enum E { V } pub f() { () } }",
        "type Borrowed<'a, T, E: EffectRow> = &'a T; type Double = ((u8)); enum GroupedPayload { V((u8), ((u16))) }",
        "type View<'a, T> = core::View<'a, T>; borrow<'a, T>(value: &'a T) -> View<'a, T> { unreachable() }",
        "type First = u8; effect Ignored { ping() -> !; } struct Middle { value: First } enum Last { Done }",
        "pub effect Control<'a, T, E: EffectRow> where T: Marker { [0, infinity] choose<U>(input: &'a T, fallback: U) -> Result<T, U> where U: Marker; [2, 4] repeat(value: T) -> T; stop(reason: String) -> !; unit() ->; implicit() }",
        "effect Adjacent { first() second(value: u8) -> u8 third() -> ! }",
        "effect AdjacentWhere<T> { first(value: T) -> T where T: Marker second<U>(value: U) -> U }",
        "effect GenericWhere<T> { first<F, U>(value: T, function: F) -> U where Vec<Result<T, U>>: Marker, F: Fn<(T), Output=U> next<V>(value: V) -> V }",
        "infixl 30 +; infixr 1 else; infix 50 ==; prefix 90 !;",
        "prefix 0 not; infixl 0xFF <*>; infixr 0b1_000 cons; infix 2_5_5 &=;",
        "infixl 35 <*>=; prefix 99 !!; infix 17 &=;",
        "type BeforeFixity = u8; infixl 42 combine; use dependency; trait Marker {} struct AfterFixity {} prefix 7 ~; let global = (); enum LastFixity {}",
        "mod fixities { pub infixr 1 otherwise; infixl 40 <*>; pub type Local = u8; } prefix 90 not;",
        "mod left { infixl 5 join; } mod right { pub infixl 5 join; }",
        "pub prefix 255 negate; pub infixr 0 choose; private_name() { () }",
        "struct Unsupported<const N: u32> { value: u8 }",
        "enum ConstEnum<const N: u32> { One }",
        "const_generic<const Q: Quantity>() -> () { () }",
    ];
    let malformed = [
        "type Missing = ;",
        "type Bad = u8 u16;",
        "struct Bad { value u8 }",
        "struct Bad { value: Vec<> }",
        "struct Bad trailing {}",
        "enum Bad { Some(Vec<>) }",
        "enum Bad { Variant { value: u8 } }",
        "type UnsupportedArray = [u8; 4];",
        "infixl 256 too_high;",
        "infixr 1.5 fractional;",
        "infix 40 ;",
        "infixl 30 + +;",
        "infixl 30 ::;",
        "infixr 30 ->;",
        "prefix 30 .;",
        "infix 30 where;",
        "effect MissingName { [0, 1] (value: u8) -> u8; }",
        "effect BadQuantity { [0 1] choose() -> u8; }",
        "effect BadUpper { [0, nope] choose() -> u8; }",
        "effect BadParameter { choose(value u8) -> u8; }",
        "effect BadWhere where { choose() -> u8; }",
        "effect BadOperationWhere { choose() -> u8 where; }",
        "invoke<F: NotAParameterKind>(body: F) -> F { body }",
        "trait Read { read(self: &Self) -> i64 }",
    ];
    let mut paths = Vec::new();
    for (index, source) in valid.into_iter().enumerate() {
        let path = directory.join(format!("valid-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    for (index, source) in malformed.into_iter().enumerate() {
        let path = directory.join(format!("error-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }

    let mut deep = String::from("type Deep = ");
    for _ in 0..32 {
        deep.push_str("Vec<");
    }
    deep.push_str("u8");
    for _ in 0..32 {
        deep.push('>');
    }
    deep.push(';');
    let path = directory.join("valid-deep.glorious");
    fs::write(&path, deep).unwrap();
    paths.push(path);
    paths
}

#[test]
fn rust_interface_oracle_classifies_the_focused_corpus() {
    let directory = tempfile::tempdir().unwrap();
    let corpus = corpus(directory.path());
    for path in &corpus {
        let mut encoded = Vec::new();
        encode_rust_interfaces(&mut encoded, &fs::read_to_string(path).unwrap());
        let expected = if path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .starts_with("valid-")
        {
            0
        } else {
            3
        };
        assert_eq!(
            encoded.first().copied(),
            Some(expected),
            "unexpected Rust-oracle status for input {}",
            path.display()
        );
    }
}

#[test]
fn self_hosted_interfaces_match_rust_in_vm_and_native_execution() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            if std::env::var_os("G1_SELF_HOST_INTERFACES_CHECK_ONLY").is_some() {
                let phases = grandiose::compile_bundle_to_phases_with_options(
                    &self_host_bundle(),
                    CompileOptions {
                        optimization_level: OptimizationLevel::O0,
                    },
                )
                .unwrap();
                verify(phases.artifact).unwrap();
                return;
            }

            let directory = tempfile::tempdir().unwrap();
            let corpus = corpus(directory.path());
            let expected_path = directory.path().join("expected.bin");
            let vm_path = directory.path().join("vm.bin");
            let mut expected = Vec::new();
            push_u32(&mut expected, corpus.len().try_into().unwrap());
            for path in &corpus {
                encode_rust_interfaces(&mut expected, &fs::read_to_string(path).unwrap());
            }
            fs::write(&expected_path, &expected).unwrap();

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let verified = verify(phases.artifact.clone()).unwrap();
            for (index, path) in corpus.iter().enumerate() {
                let vm_one_path = directory.path().join(format!("vm-{index}.bin"));
                let vm = Vm::with_host(
                    verified.clone(),
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![
                        vm_one_path.clone().into_os_string(),
                        path.clone().into_os_string(),
                    ]),
                )
                .unwrap();
                assert_eq!(
                    vm.run(entry, vec![]).unwrap_or_else(|error| {
                        panic!("VM input {index} ({}) failed: {error:?}", path.display())
                    }),
                    Value::Unit
                );
                let mut expected_one = Vec::new();
                push_u32(&mut expected_one, 1);
                encode_rust_interfaces(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&vm_one_path).unwrap(),
                    expected_one,
                    "VM interfaces diverged for input {index} ({})",
                    path.display()
                );
            }
            let vm_args = std::iter::once(vm_path.clone().into_os_string())
                .chain(corpus.iter().map(|path| path.clone().into_os_string()))
                .collect::<Vec<OsString>>();
            let vm = Vm::with_host(
                verified,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vm_args),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_eq!(
                fs::read(&vm_path).unwrap(),
                expected,
                "VM interfaces diverged"
            );

            let asan = std::env::var_os("G1_SELF_HOST_INTERFACES_ASAN").is_some();
            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let debug_directory = repository_root().join("target/self-host-interfaces-debug");
            if asan {
                fs::create_dir_all(&debug_directory).unwrap();
                let functions = phases
                    .mir
                    .functions
                    .iter()
                    .enumerate()
                    .map(|(index, function)| format!("{index}\t{}\n", function.name))
                    .collect::<String>();
                fs::write(debug_directory.join("functions.txt"), functions).unwrap();
            }
            let llvm = if asan {
                debug_directory.join("self-host-interfaces.ll")
            } else {
                directory.path().join("self-host-interfaces.ll")
            };
            let executable = if asan {
                debug_directory.join("self-host-interfaces")
            } else {
                directory.path().join("self-host-interfaces")
            };
            fs::write(&llvm, module.ir).unwrap();
            let mut clang_command = Command::new("clang");
            clang_command
                .arg(&llvm)
                .arg(repository_root().join("crates/grandiose/src/native_runtime.c"))
                .arg(repository_root().join("crates/grandiose/src/native_host_runtime.c"))
                .arg("-O0");
            if asan {
                clang_command.args(["-fsanitize=address", "-fno-omit-frame-pointer", "-g"]);
            }
            let clang = clang_command.arg("-o").arg(&executable).output().unwrap();
            assert!(
                clang.status.success(),
                "{}",
                String::from_utf8_lossy(&clang.stderr)
            );

            let native_all_path = directory.path().join("native-all.bin");
            let native_all = Command::new(&executable)
                .arg(&native_all_path)
                .args(&corpus)
                .output()
                .unwrap();
            assert!(
                native_all.status.success(),
                "native whole-corpus status: {:?}\n{}",
                native_all.status,
                String::from_utf8_lossy(&native_all.stderr)
            );
            assert_eq!(
                fs::read(&native_all_path).unwrap(),
                expected,
                "native whole-corpus interfaces diverged"
            );
            for (index, path) in corpus.iter().enumerate() {
                let native_path = directory.path().join(format!("native-{index}.bin"));
                let native = Command::new(&executable)
                    .arg(&native_path)
                    .arg(path)
                    .output()
                    .unwrap();
                assert!(
                    native.status.success(),
                    "native input {index} ({}) status: {:?}\n{}",
                    native.status,
                    path.display(),
                    String::from_utf8_lossy(&native.stderr)
                );
                let mut expected_one = Vec::new();
                push_u32(&mut expected_one, 1);
                encode_rust_interfaces(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&native_path).unwrap(),
                    expected_one,
                    "native interfaces diverged for input {index} ({})",
                    path.display()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_unit_nested_generic_nominal_fields_construct_and_forward() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("nested-generic-fields.glorious");
    let output = directory.path().join("nested-generic-fields.grbc");
    fs::write(&input, NESTED_GENERIC_NOMINAL_FIELDS).unwrap();

    let bootstrap_answers = [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ]
    .into_iter()
    .map(|optimization_level| {
        let phases = grandiose::compile_source_to_phases_with_options(
            "nested-generic-fields.glorious",
            NESTED_GENERIC_NOMINAL_FIELDS,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let answer = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        let verified = verify(phases.artifact).unwrap();
        Vm::new(verified).run(answer, vec![]).unwrap()
    })
    .collect::<Vec<_>>();
    assert_eq!(bootstrap_answers, vec![Value::U64(0); 3]);

    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    let entry = phases.artifact.entry_function.unwrap();
    let compiler = verify(phases.artifact).unwrap();
    let vm = Vm::with_host(
        compiler,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);

    let encoded = fs::read(output).unwrap();
    assert_eq!(&encoded[..5], &[1, 0, 0, 0, 0]);
}
