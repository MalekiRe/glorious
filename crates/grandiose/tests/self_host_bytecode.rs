use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    CompileOptions, LlvmOptions, OptimizationLevel,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{
    Artifact, SystemHost, Type, Value, Vm,
    bytecode::{I64, Instruction, U64},
    verify::load_verified,
};

const FIXTURE: &str = r#"
    struct Pair {
        first: i64,
        second: i64
    }

    enum Choice {
        Empty,
        Number(i64),
        Pair(i64, u64)
    }

    identity(value: i64) -> i64 { value }
    answer() -> i64 {
        let value = 7;
        identity(value)
    }
    first() -> i64 {
        let pair = (7, 9);
        pair.0
    }
    struct_answer() -> i64 {
        let value = 11;
        let pair = Pair { second: value, first: value };
        pair.first
    }
    empty_choice() -> Choice { Choice::Empty }
    number_choice() -> Choice { Choice::Number(13) }
    pair_choice() -> Choice { Choice::Pair(7, 9) }
    inspect_choice(choice: Choice) -> i64 {
        handle choice {
            Choice::Empty => 3,
            Choice::Number(value) => value,
            Choice::Pair(first, _) => first
        }
    }
    inspect_choice_tail(choice: Choice) -> u64 {
        handle choice {
            Choice::Empty => 3,
            Choice::Number(_) => 13,
            Choice::Pair(_, second) => second
        }
    }
    matched_empty() -> i64 { inspect_choice(Choice::Empty) }
    matched_number() -> i64 { inspect_choice(Choice::Number(13)) }
    matched_pair() -> i64 { inspect_choice(Choice::Pair(7, 9)) }
    matched_pair_tail() -> u64 { inspect_choice_tail(Choice::Pair(7, 9)) }
    main() { () }
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
        r#"
            mod frontend;
            mod backend;
            mod compiler;
            use compiler::CompileError;

            classify_compile_error(source: String) -> u8 {
                handle compiler::compile_source(&source) {
                    Result::Ok(_) => 0,
                    Result::Err(error) => handle error {
                        CompileError::Lex(_) => 1,
                        CompileError::Scan(_) => 2,
                        CompileError::Headers(_) => 3,
                        CompileError::ResolutionIndex(_) => 4,
                        CompileError::InterfaceCollection(_) => 5,
                        CompileError::DeclarationName(_) => 6,
                        CompileError::BodyParse(_, _) => 7,
                        CompileError::BodyResolution(_, _) => 8,
                        CompileError::BodyElaboration(_, _) => 9,
                        CompileError::Lowering(_, _) => 10,
                        CompileError::InterfaceName(_) => 11,
                        CompileError::UnsupportedInterfaceType(_) => 12,
                        CompileError::Emission(_) => 13
                    }
                }
            }

            main() { run_compiler_host(compiler::application) }
        "#,
    );
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("frontend/bodies/bodies.glorious"),
        root.join("frontend/resolution/resolution.glorious"),
        root.join("frontend/elaboration/elaboration.glorious"),
        root.join("backend/backend.glorious"),
        root.join("backend/artifact/artifact.glorious"),
        root.join("backend/lowering/lowering.glorious"),
        root.join("backend/emission/emission.glorious"),
        root.join("compiler/compiler.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let source = fs::read_to_string(&path).unwrap();
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

fn function_id(artifact: &Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("self-hosted artifact is missing `{name}`")) as u32
}

fn assert_compiled_artifact(bytes: &[u8]) {
    let decoded = Artifact::decode(bytes).expect("self-hosted GRBC must decode");
    assert_eq!(
        decoded.encode(),
        bytes,
        "self-hosted GRBC must already be canonical"
    );
    let answer = function_id(&decoded, "answer");
    let first = function_id(&decoded, "first");
    let struct_answer = function_id(&decoded, "struct_answer");
    let empty_choice = function_id(&decoded, "empty_choice");
    let number_choice = function_id(&decoded, "number_choice");
    let pair_choice = function_id(&decoded, "pair_choice");
    let matched_empty = function_id(&decoded, "matched_empty");
    let matched_number = function_id(&decoded, "matched_number");
    let matched_pair = function_id(&decoded, "matched_pair");
    let matched_pair_tail = function_id(&decoded, "matched_pair_tail");
    let main = function_id(&decoded, "main");
    assert!(decoded.types.iter().any(|ty| matches!(
        ty.representation(),
        Type::Struct { name, fields, .. }
            if name == "Pair"
                && fields.len() == 2
                && fields[0].name == "first"
                && fields[1].name == "second"
    )));
    let choice = decoded
        .types
        .iter()
        .position(|ty| {
            matches!(
                ty.representation(),
                Type::Enum { name, .. } if name == "Choice"
            )
        })
        .expect("self-hosted artifact must contain Choice") as u32;
    let Type::Enum { variants, .. } = decoded.types[choice as usize].representation() else {
        unreachable!()
    };
    assert_eq!(
        variants
            .iter()
            .map(|variant| variant.name.as_str())
            .collect::<Vec<_>>(),
        ["Empty", "Number", "Pair"]
    );
    assert!(variants[0].fields.is_empty());
    assert_eq!(variants[1].fields.len(), 1);
    assert_eq!(variants[1].fields[0].name, "0");
    assert_eq!(variants[1].fields[0].ty, I64);
    assert_eq!(variants[2].fields.len(), 2);
    assert_eq!(variants[2].fields[0].name, "0");
    assert_eq!(variants[2].fields[0].ty, I64);
    assert_eq!(variants[2].fields[1].name, "1");
    assert_eq!(variants[2].fields[1].ty, U64);
    let verified = load_verified(bytes).expect("self-hosted GRBC must verify");
    assert_eq!(
        Vm::new(verified.clone()).run(answer, vec![]).unwrap(),
        Value::I64(7)
    );
    assert_eq!(
        Vm::new(verified.clone()).run(first, vec![]).unwrap(),
        Value::I64(7)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(struct_answer, vec![])
            .unwrap(),
        Value::I64(11)
    );
    assert_eq!(
        Vm::new(verified.clone()).run(empty_choice, vec![]).unwrap(),
        Value::aggregate_with_variant(choice, Some(0), [])
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(number_choice, vec![])
            .unwrap(),
        Value::aggregate_with_variant(choice, Some(1), [Value::I64(13)])
    );
    assert_eq!(
        Vm::new(verified.clone()).run(pair_choice, vec![]).unwrap(),
        Value::aggregate_with_variant(choice, Some(2), [Value::I64(7), Value::U64(9)])
    );
    assert!(
        decoded
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::EnumTag { .. })),
        "enum handles must inspect the subject tag"
    );
    assert!(
        decoded
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Switch { .. })),
        "enum handles must branch on the subject tag"
    );
    assert!(
        decoded
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::ProjectMove { .. })),
        "enum handles must move payload fields into arm bindings"
    );
    assert!(
        decoded
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Deconstruct { .. })),
        "enum handles must consume the matched aggregate shell"
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(matched_empty, vec![])
            .unwrap(),
        Value::I64(3)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(matched_number, vec![])
            .unwrap(),
        Value::I64(13)
    );
    assert_eq!(
        Vm::new(verified.clone()).run(matched_pair, vec![]).unwrap(),
        Value::I64(7)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(matched_pair_tail, vec![])
            .unwrap(),
        Value::U64(9)
    );
    assert_eq!(Vm::new(verified).run(main, vec![]).unwrap(), Value::Unit);
}

#[test]
fn self_hosted_frontend_emits_canonical_executable_bytecode_in_vm_and_native() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("input.glorious");
            fs::write(&input, FIXTURE).unwrap();

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let compiler_entry = phases.artifact.entry_function.unwrap();
            let compiler = grandiose_vm::verify(phases.artifact.clone()).unwrap();
            let classify = function_id(&phases.artifact, "classify_compile_error");
            for (source, expected) in [("\"", 1), ("}", 2), ("struct Broken { field }", 3)] {
                assert_eq!(
                    Vm::with_host(
                        compiler.clone(),
                        ["process.args", "fs.read", "fs.write", "diagnostic"],
                        SystemHost::new(vec![]),
                    )
                    .unwrap()
                    .run(classify, vec![Value::Text(source.into())])
                    .unwrap(),
                    Value::U64(expected),
                    "{source:?}"
                );
            }

            let vm_output = directory.path().join("vm.grbc");
            let vm = Vm::with_host(
                compiler,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![
                    vm_output.clone().into_os_string(),
                    input.clone().into_os_string(),
                ]),
            )
            .unwrap();
            assert_eq!(vm.run(compiler_entry, vec![]).unwrap(), Value::Unit);
            let vm_bytes = fs::read(&vm_output).unwrap();
            assert_compiled_artifact(&vm_bytes);

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-bytecode.ll");
            let executable = directory.path().join("self-host-bytecode");
            fs::write(&llvm, module.ir).unwrap();
            let clang = Command::new("clang")
                .arg(&llvm)
                .arg(repository_root().join("crates/grandiose/src/native_runtime.c"))
                .arg(repository_root().join("crates/grandiose/src/native_host_runtime.c"))
                .arg("-O0")
                .arg("-o")
                .arg(&executable)
                .output()
                .unwrap();
            assert!(
                clang.status.success(),
                "{}",
                String::from_utf8_lossy(&clang.stderr)
            );

            let native_output = directory.path().join("native.grbc");
            let native = Command::new(&executable)
                .arg(&native_output)
                .arg(&input)
                .output()
                .unwrap();
            assert!(
                native.status.success(),
                "native self-host compiler failed: {:?}\n{}",
                native.status,
                String::from_utf8_lossy(&native.stderr)
            );
            let native_bytes = fs::read(&native_output).unwrap();
            assert_eq!(native_bytes, vm_bytes, "VM and LLVM hosts must agree");
            assert_compiled_artifact(&native_bytes);
        })
        .unwrap()
        .join()
        .unwrap();
}
