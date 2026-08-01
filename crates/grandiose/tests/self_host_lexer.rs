use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    CompileOptions, LlvmOptions, OptimizationLevel,
    lexer::{Kw, NumberBase, Token, TokenKind},
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
        "mod frontend;\nmod probe;\n\nmain() { run_compiler_host(probe::lexer::application) }\n",
    );
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("probe/probe.glorious"),
        root.join("probe/lexer/lexer.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let source = fs::read_to_string(&path)
                .unwrap()
                .replace("pub mod scanner;\n", "")
                .replace("pub mod headers;\n", "")
                .replace("pub mod bodies;\n", "")
                .replace("pub mod resolution;\n", "")
                .replace("pub mod elaboration;\n", "");
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

fn push_u16(output: &mut Vec<u8>, value: u16) {
    output.extend(value.to_le_bytes());
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

fn keyword_code(keyword: Kw) -> u8 {
    match keyword {
        Kw::Cancel => 1,
        Kw::Effect => 2,
        Kw::Enum => 3,
        Kw::Handle => 4,
        Kw::Impl => 5,
        Kw::Is => 6,
        Kw::Let => 7,
        Kw::Perform => 8,
        Kw::Resume => 9,
        Kw::Struct => 10,
        Kw::Tail => 11,
        Kw::Trait => 12,
        Kw::Type => 13,
        Kw::Where => 14,
    }
}

fn token_code(kind: &TokenKind) -> u16 {
    match kind {
        TokenKind::Ident(_) => 1,
        TokenKind::Keyword(_) => 2,
        TokenKind::Lifetime(_) => 3,
        TokenKind::Number(_) => 4,
        TokenKind::String(_) => 5,
        TokenKind::Char(_) => 6,
        TokenKind::Byte(_) => 7,
        TokenKind::ByteString(_) => 8,
        TokenKind::Label(_) => 9,
        TokenKind::Operator(_) => 10,
        TokenKind::LParen => 11,
        TokenKind::RParen => 12,
        TokenKind::LBrace => 13,
        TokenKind::RBrace => 14,
        TokenKind::LBracket => 15,
        TokenKind::RBracket => 16,
        TokenKind::Comma => 17,
        TokenKind::Colon => 18,
        TokenKind::DoubleColon => 19,
        TokenKind::DotDot => 20,
        TokenKind::Dot => 21,
        TokenKind::Semicolon => 22,
        TokenKind::Arrow => 23,
        TokenKind::FatArrow => 24,
        TokenKind::Slash => 25,
        TokenKind::Plus => 26,
        TokenKind::Minus => 27,
        TokenKind::Star => 28,
        TokenKind::Percent => 29,
        TokenKind::Pipe => 30,
        TokenKind::Eq => 31,
        TokenKind::EqEq => 32,
        TokenKind::BangEq => 33,
        TokenKind::Lt => 34,
        TokenKind::LtEq => 35,
        TokenKind::Gt => 36,
        TokenKind::GtEq => 37,
        TokenKind::Amp => 38,
        TokenKind::Bang => 39,
        TokenKind::Dollar => 40,
        TokenKind::Eof => 41,
    }
}

fn encode_token(output: &mut Vec<u8>, token: &Token) {
    push_u16(output, token_code(&token.kind));
    push_u64(output, token.span.start as u64);
    push_u64(output, token.span.end as u64);
    match &token.kind {
        TokenKind::Ident(text)
        | TokenKind::Lifetime(text)
        | TokenKind::String(text)
        | TokenKind::Label(text)
        | TokenKind::Operator(text) => push_bytes(output, text.as_bytes()),
        TokenKind::Keyword(keyword) => output.push(keyword_code(*keyword)),
        TokenKind::Number(number) => {
            push_bytes(output, number.spelling.as_bytes());
            output.push(match number.base {
                NumberBase::Binary => 1,
                NumberBase::Octal => 2,
                NumberBase::Decimal => 3,
                NumberBase::Hex => 4,
            });
            push_bytes(output, number.digits.as_bytes());
            match &number.fraction {
                Some(fraction) => {
                    output.push(1);
                    push_bytes(output, fraction.as_bytes());
                }
                None => output.push(0),
            }
            match &number.exponent {
                Some(exponent) => {
                    output.push(1);
                    output.push(u8::from(exponent.negative));
                    push_bytes(output, exponent.digits.as_bytes());
                }
                None => output.push(0),
            }
        }
        TokenKind::Char(value) => push_u32(output, *value as u32),
        TokenKind::Byte(value) => output.push(*value),
        TokenKind::ByteString(value) => push_bytes(output, value),
        _ => {}
    }
}

fn error_code(title: &str) -> u16 {
    match title {
        "unexpected character" => 1,
        "unfinished comment" => 2,
        "invalid label" => 3,
        "invalid digit" => 4,
        "misplaced digit separator" => 5,
        "expected digits" => 6,
        "malformed float exponent" => 7,
        "unfinished escape" => 8,
        "invalid character escape" => 9,
        "unknown escape" => 10,
        "malformed hex escape" => 11,
        "malformed Unicode escape" => 12,
        "unfinished Unicode escape" => 13,
        "invalid Unicode scalar" => 14,
        "invalid byte escape" => 15,
        "unfinished string" => 16,
        "invalid byte string character" => 17,
        "unfinished byte string" => 18,
        "empty byte literal" => 19,
        "invalid byte literal" => 20,
        "unfinished byte literal" => 21,
        "unfinished character literal" => 22,
        "empty character literal" => 23,
        "invalid lifetime identifier" => 24,
        "invalid character literal" => 25,
        "lexer resource limit" => 26,
        other => panic!("unmapped lexer error title `{other}`"),
    }
}

fn encode_rust_lex(output: &mut Vec<u8>, source: &str) {
    match grandiose::lexer::lex(source) {
        Ok(tokens) => {
            output.push(0);
            push_u32(output, tokens.len().try_into().unwrap());
            for token in &tokens {
                encode_token(output, token);
            }
        }
        Err(error) => {
            output.push(1);
            push_u16(output, error_code(&error.title));
            let span = error.span.unwrap();
            push_u64(output, span.start as u64);
            push_u64(output, span.end as u64);
        }
    }
}

fn collect_glorious_files(directory: &Path, output: &mut Vec<PathBuf>) {
    let mut entries = fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if path
            .components()
            .any(|component| component.as_os_str() == "target")
        {
            continue;
        }
        if path.is_dir() {
            collect_glorious_files(&path, output);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "glorious")
        {
            output.push(path);
        }
    }
}

fn corpus(directory: &Path) -> Vec<PathBuf> {
    let focused = [
        "",
        "cancel effect enum handle impl is let perform resume struct tail trait type where",
        "alpha beta-name _hidden @done $value :: : .. . -> => == != <= >=",
        "0 1_000 0b_1010 0o755 0x_ff 12.50 6.02e+23 pair.0.1",
        r#""plain\n\u{1f642}\x41" 'x' '\n' 'λ' 'life b"bytes\xff" b'x'"#,
        "/* outer /* nested */ done */ value // tail\nnext",
        "@",
        "0b2",
        "1_",
        "1e",
        r#""unfinished"#,
        r#"b"λ""#,
        "λ",
        "''",
        "'ab'",
        r#""\u{110000}""#,
    ];
    let mut paths = Vec::new();
    for (index, source) in focused.into_iter().enumerate() {
        let path = directory.join(format!("focused-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    // The self-host lexer is intentionally recursive. This exceeds the old
    // native driver stack limit unless cleanup-only continuations form true
    // MIR/LLVM tail calls.
    let tail_stress = directory.join("focused-tail-stress.glorious");
    fs::write(&tail_stress, " ".repeat(10_000)).unwrap();
    paths.push(tail_stress);

    let mut repository_files = Vec::new();
    collect_glorious_files(&repository_root(), &mut repository_files);
    // Keep interpreter-backed differential runs bounded. Large compiler and
    // standard-library sources are covered by the full self-host compilation
    // gate; this runtime oracle samples the repository's smaller real files.
    repository_files.retain(|path| fs::metadata(path).unwrap().len() <= 16 * 1024);
    if std::env::var_os("G1_SELF_HOST_FOCUSED_ONLY").is_some() {
        repository_files.clear();
    }
    repository_files.truncate(128);
    paths.extend(repository_files);
    paths
}

#[test]
fn self_hosted_lexer_matches_rust_in_vm_and_native_execution() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let corpus = corpus(directory.path());
            let expected_path = directory.path().join("expected.bin");
            let vm_path = directory.path().join("vm.bin");
            let native_path = directory.path().join("native.bin");
            let mut expected = Vec::new();
            push_u32(&mut expected, corpus.len().try_into().unwrap());
            for path in &corpus {
                encode_rust_lex(&mut expected, &fs::read_to_string(path).unwrap());
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
            assert_eq!(fs::read(&vm_path).unwrap(), expected, "VM lexer diverged");

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-lexer.ll");
            let executable = directory.path().join("self-host-lexer");
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
            let native = Command::new(&executable)
                .arg(&native_path)
                .args(&corpus)
                .output()
                .unwrap();
            if !native.status.success() {
                let status = native.status;
                let stderr = String::from_utf8_lossy(&native.stderr).into_owned();
                let preserved = directory.keep();
                panic!(
                    "native lexer failed with {status:?}: {stderr}\nartifacts: {}",
                    preserved.display()
                );
            }
            assert_eq!(
                fs::read(&native_path).unwrap(),
                expected,
                "native lexer diverged"
            );

            // The protocol is deterministic across independent executions.
            let repeat_path = directory.path().join("repeat.bin");
            let repeat = Command::new(executable)
                .arg(&repeat_path)
                .args(&corpus)
                .output()
                .unwrap();
            assert!(repeat.status.success());
            assert_eq!(fs::read(repeat_path).unwrap(), expected);
        })
        .unwrap()
        .join()
        .unwrap();
}
