use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    CompileOptions, LlvmOptions, OptimizationLevel,
    ast::{
        EffectRowSyntax, Function, GenericParamKind, GenericParams, TypeSyntax, TypeSyntaxKind,
        Visibility,
    },
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{SystemHost, Value, Vm, verify};

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
        "mod frontend;\nmod probe;\n\nmain() { run_compiler_host(probe::headers::application) }\n",
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

fn encode_type(output: &mut Vec<u8>, ty: &TypeSyntax) -> Result<(), ()> {
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
            encode_type(output, referent)?;
        }
        TypeSyntaxKind::UniqueReference { lifetime, referent } => {
            output.push(3);
            encode_optional_lifetime(output, lifetime.as_ref().map(|value| value.name.as_str()));
            encode_type(output, referent)?;
        }
        TypeSyntaxKind::Tuple(elements) => {
            output.push(4);
            push_u32(output, elements.len().try_into().unwrap());
            for element in elements {
                encode_type(output, element)?;
            }
        }
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            lifetime_arguments,
        } => {
            if !lifetime_arguments.is_empty() {
                return Err(());
            }
            output.push(5);
            encode_type(output, constructor)?;
            push_u32(output, arguments.len().try_into().unwrap());
            for argument in arguments {
                encode_type(output, argument)?;
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
            GenericParamKind::Const(_) => return Err(()),
        };
        output.push(kind);
        push_string(output, &parameter.name);
        if parameter.const_default.is_some() {
            return Err(());
        }
    }
    Ok(())
}

fn encode_effect_row(output: &mut Vec<u8>, row: &EffectRowSyntax) -> Result<(), ()> {
    push_u32(output, row.effects.len().try_into().unwrap());
    for effect in &row.effects {
        encode_type(output, effect)?;
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

fn encode_callable(
    output: &mut Vec<u8>,
    program: &grandiose::ast::Program,
    declaration: &Function,
) -> Result<(), ()> {
    if declaration.where_clause.is_some() {
        return Err(());
    }
    output.push(u8::from(
        program.visibility(declaration.span) == Visibility::Public,
    ));
    push_string(output, &declaration.name);
    encode_generics(output, declaration.generics.as_ref())?;
    push_u32(output, declaration.params.len().try_into().unwrap());
    for parameter in &declaration.params {
        push_string(output, &parameter.name);
        encode_type(output, &parameter.ty)?;
    }
    match &declaration.return_type {
        Some(return_type) => {
            output.push(1);
            encode_type(output, return_type)?;
        }
        None => output.push(0),
    }
    match &declaration.outward_effects {
        Some(effects) => {
            output.push(1);
            encode_effect_row(output, effects)?;
        }
        None => output.push(0),
    }
    Ok(())
}

fn encode_rust_headers(output: &mut Vec<u8>, source: &str) {
    let Ok(tokens) = grandiose::lexer::lex(source) else {
        output.push(1);
        return;
    };
    let Ok(program) = grandiose::parser::parse(tokens) else {
        output.push(3);
        return;
    };
    let mut callables = program.functions.iter().collect::<Vec<_>>();
    callables.sort_by_key(|declaration| declaration.span.start);

    let mut encoded = Vec::new();
    push_u32(&mut encoded, callables.len().try_into().unwrap());
    for callable in callables {
        if encode_callable(&mut encoded, &program, callable).is_err() {
            output.push(3);
            return;
        }
    }
    output.push(0);
    output.extend(encoded);
}

fn corpus(directory: &Path) -> Vec<PathBuf> {
    let focused = [
        "",
        "noop() { () }",
        "identity<T>(value: T) -> T { value }",
        "pub consume(value: &mut Vec<u8>) { () }",
        "borrow<'a, T>(value: &'a T) -> &'a T { value }",
        "tuples(unit: (), single: (u8,), trio: (u8, String, !)) -> (u8, u8) { (0, 0) }",
        "view<T>(value: pkg::View<(T, !)>) -> pkg::View<(T, !)> { value }",
        "first<T>(value: Vec<T>) -> T { unreachable() } second(value: core::Pair<u8, u16>) { () }",
        "spaced<T,>(value: Vec< /* element */ T, >) -> Vec<T> { value }",
        "read<T, E: EffectRow>(value: T) -> pkg::Result<T, !> / {Console, Io<T> | E} { value }",
        "write(value: String) / Console { () }",
        "bad(value u32) { () }",
        "bad(value: Vec<>) { () }",
        "bad(value: T) trailing { () }",
    ];
    let mut paths = Vec::new();
    for (index, source) in focused.into_iter().enumerate() {
        let path = directory.join(format!("focused-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }

    let mut deep = String::from("deep(value: ");
    for _ in 0..32 {
        deep.push_str("Vec<");
    }
    deep.push_str("u8");
    for _ in 0..32 {
        deep.push('>');
    }
    deep.push_str(") { () }");
    let path = directory.join("deep.glorious");
    fs::write(&path, deep).unwrap();
    paths.push(path);
    paths
}

#[test]
fn self_hosted_headers_match_rust_in_vm_and_native_execution() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            if std::env::var_os("G1_SELF_HOST_HEADERS_CHECK_ONLY").is_some() {
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
                encode_rust_headers(&mut expected, &fs::read_to_string(path).unwrap());
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
            let vm_args = std::iter::once(vm_path.clone().into_os_string())
                .chain(corpus.iter().map(|path| path.clone().into_os_string()))
                .collect::<Vec<OsString>>();
            let vm = Vm::with_host(
                verify(phases.artifact.clone()).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vm_args),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_eq!(fs::read(&vm_path).unwrap(), expected, "VM headers diverged");

            let asan = std::env::var_os("G1_SELF_HOST_HEADERS_ASAN").is_some();
            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let debug_directory = repository_root().join("target/self-host-headers-debug");
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
                debug_directory.join("self-host-headers.ll")
            } else {
                directory.path().join("self-host-headers.ll")
            };
            let executable = if asan {
                debug_directory.join("self-host-headers")
            } else {
                directory.path().join("self-host-headers")
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
                "native whole-corpus headers diverged"
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
                encode_rust_headers(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&native_path).unwrap(),
                    expected_one,
                    "native headers diverged for input {index} ({})",
                    path.display()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
