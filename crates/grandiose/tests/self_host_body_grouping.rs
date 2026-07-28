use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    CompileOptions, LlvmOptions, OptimizationLevel,
    ast::{BinaryOp, Expr, ExprKind, Program, Stmt, UnaryOp},
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
        "mod frontend;\n\nmain() { run_compiler_host(frontend::bodies::application) }\n",
    );
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("frontend/bodies/bodies.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let source = fs::read_to_string(&path).unwrap();
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

fn push_string(output: &mut Vec<u8>, value: &str) {
    push_u32(output, value.len().try_into().unwrap());
    output.extend(value.as_bytes());
}

fn binary_spelling(operator: BinaryOp) -> &'static str {
    match operator {
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Rem => "%",
        BinaryOp::Eq => "==",
        BinaryOp::NotEq => "!=",
        BinaryOp::Lt => "<",
        BinaryOp::LtEq => "<=",
        BinaryOp::Gt => ">",
        BinaryOp::GtEq => ">=",
    }
}

fn unary_spelling(operator: UnaryOp) -> &'static str {
    match operator {
        UnaryOp::Negate => "-",
        UnaryOp::BorrowShared => "&",
        UnaryOp::BorrowUnique => "&mut",
        UnaryOp::Dereference => "*",
    }
}

fn call_operator<'a>(callee: &'a Expr, arity: usize) -> Option<&'a str> {
    let ExprKind::Variable(path) = &callee.kind else {
        return None;
    };
    match (path.as_ref(), arity) {
        ([operator], 1 | 2) => Some(operator),
        ([trait_name, operator], 2)
            if matches!(
                (trait_name.as_ref(), operator.as_ref()),
                ("Add", "+") | ("Equal", "==") | ("Less", "<") | ("Greater", ">")
            ) =>
        {
            Some(operator)
        }
        _ => None,
    }
}

fn encode_expression(output: &mut Vec<u8>, program: &Program, expression: &Expr) -> Result<(), ()> {
    match &expression.kind {
        ExprKind::Variable(path) if path.len() == 1 => {
            output.push(1);
            push_string(output, &path[0]);
        }
        ExprKind::Int(_) => {
            let literal = program.numeric_literal(expression.span).ok_or(())?;
            let value = literal.as_u64(expression.span).map_err(|_| ())?;
            output.push(2);
            push_u64(output, value);
        }
        ExprKind::Unit => output.push(3),
        ExprKind::Call(callee, arguments) if matches!(arguments.len(), 1 | 2) => {
            let operator = call_operator(callee, arguments.len()).ok_or(())?;
            match arguments.len() {
                1 => {
                    output.push(5);
                    push_string(output, operator);
                    encode_expression(output, program, &arguments[0])?;
                }
                2 => {
                    output.push(6);
                    push_string(output, operator);
                    encode_expression(output, program, &arguments[0])?;
                    encode_expression(output, program, &arguments[1])?;
                }
                _ => unreachable!(),
            }
        }
        ExprKind::Binary { op, lhs, rhs } => {
            output.push(6);
            push_string(output, binary_spelling(*op));
            encode_expression(output, program, lhs)?;
            encode_expression(output, program, rhs)?;
        }
        ExprKind::Unary { op, operand } => {
            output.push(5);
            push_string(output, unary_spelling(*op));
            encode_expression(output, program, operand)?;
        }
        _ => return Err(()),
    }
    Ok(())
}

fn final_expression(function: &grandiose::ast::Function) -> Option<&Expr> {
    let ExprKind::Block(statements) = &function.body.kind else {
        return None;
    };
    let Stmt::Expr(expression) = statements.last()? else {
        return None;
    };
    Some(expression)
}

fn raw_source_bundle(source: &str) -> SourceBundle {
    SourceBundle::raw_with_trusted_standard_for_conformance(
        Segment::new("<empty-std>", ""),
        Segment::new("body-grouping-input.glorious", source),
        [],
    )
}

fn encode_rust_grouping(output: &mut Vec<u8>, source: &str) {
    let Ok(program) = grandiose::modules::parse_bundle(&raw_source_bundle(source)) else {
        output.push(3);
        return;
    };
    let mut functions = program
        .functions
        .iter()
        .filter(|function| function.name.starts_with("probe_"))
        .collect::<Vec<_>>();
    functions.sort_by_key(|function| function.span.start);

    let mut encoded = Vec::new();
    push_u32(&mut encoded, functions.len().try_into().unwrap());
    for function in functions {
        push_string(&mut encoded, &function.name);
        let Some(expression) = final_expression(function) else {
            output.push(3);
            return;
        };
        if encode_expression(&mut encoded, &program, expression).is_err() {
            output.push(3);
            return;
        }
    }
    output.push(0);
    output.extend(encoded);
}

fn corpus(directory: &Path) -> Vec<PathBuf> {
    let valid = [
        "probe_ident() { alpha }",
        "probe_u64() { 18_446_744_073_709_551_615 }",
        "probe_unit() { () }",
        "infixl 30 <+>; probe_left() { a <+> b <+> c }",
        "infixr 30 cons; probe_right() { a cons b cons c }",
        "infixl 10 low; infixl 20 high; probe_precedence() { a low b high c }",
        "infixl 10 low; infixl 20 high; probe_parentheses() { (a low b) high c }",
        "infix 10 eqish; probe_nonassoc_grouped() { (a eqish b) eqish c }",
        "prefix 90 !!; probe_prefix_nested() { !! !! value }",
        "prefix 50 neg; infixl 60 tight; infixl 40 loose; probe_prefix_precedence() { neg a tight b loose c }",
        "infixr 20 otherwise; probe_word() { first otherwise second otherwise third }",
        "infixl 35 <*>=; probe_adjacent_operator() { a <*>= b <*>= c }",
        "infixl 10 join; \
         probe_root() { a join b join c } \
         mod local { infixr 10 join; probe_local() { a join b join c } } \
         mod fallback { probe_fallback() { a join b join c } }",
    ];
    let malformed = [
        "infixl 10 op; probe_missing_operand() { a op }",
        "infixl 10 op; probe_malformed_group() { (a op) }",
        "probe_undeclared() { a <*>= b }",
        "infixl 10 leftish; infixr 10 rightish; \
         probe_mixed() { a leftish b rightish c }",
        "infix 10 eqish; probe_nonassoc() { a eqish b eqish c }",
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
    paths
}

#[test]
fn rust_body_grouping_oracle_classifies_and_encodes_the_focused_corpus() {
    let directory = tempfile::tempdir().unwrap();
    let corpus = corpus(directory.path());
    for path in &corpus {
        let source = fs::read_to_string(path).unwrap();
        let mut encoded = Vec::new();
        encode_rust_grouping(&mut encoded, &source);
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
            "unexpected Rust-oracle status for input {}: {encoded:?}",
            path.display()
        );
    }
}

#[test]
fn self_hosted_body_grouping_matches_rust_in_vm_and_native_execution() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            if std::env::var_os("G1_SELF_HOST_BODY_GROUPING_CHECK_ONLY").is_some() {
                grandiose::compile_bundle_to_phases_with_options(
                    &self_host_bundle(),
                    CompileOptions {
                        optimization_level: OptimizationLevel::O0,
                    },
                )
                .unwrap();
                return;
            }

            let directory = tempfile::tempdir().unwrap();
            let corpus = corpus(directory.path());
            let expected_path = directory.path().join("expected.bin");
            let vm_path = directory.path().join("vm.bin");
            let mut expected = Vec::new();
            push_u32(&mut expected, corpus.len().try_into().unwrap());
            for path in &corpus {
                encode_rust_grouping(&mut expected, &fs::read_to_string(path).unwrap());
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
                encode_rust_grouping(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&vm_one_path).unwrap(),
                    expected_one,
                    "VM body grouping diverged for input {index} ({})",
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
                "VM body grouping diverged"
            );

            let asan = std::env::var_os("G1_SELF_HOST_BODY_GROUPING_ASAN").is_some();
            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let debug_directory = repository_root().join("target/self-host-body-grouping-debug");
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
                debug_directory.join("self-host-body-grouping.ll")
            } else {
                directory.path().join("self-host-body-grouping.ll")
            };
            let executable = if asan {
                debug_directory.join("self-host-body-grouping")
            } else {
                directory.path().join("self-host-body-grouping")
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
                "native whole-corpus body grouping diverged"
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
                encode_rust_grouping(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&native_path).unwrap(),
                    expected_one,
                    "native body grouping diverged for input {index} ({})",
                    path.display()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
