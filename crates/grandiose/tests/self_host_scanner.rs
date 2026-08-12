use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicBool, Ordering},
};

use grandiose::{
    CompileOptions, OptimizationLevel,
    lexer::{Kw, Token, TokenKind},
    parser,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{SystemHost, Value, Vm, verify};

#[path = "support/native_incremental.rs"]
mod native_incremental;

static CONTEXTUAL_PUB_ONLY: AtomicBool = AtomicBool::new(false);
static FIXITY_ONLY: AtomicBool = AtomicBool::new(false);

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
}

fn self_host_bundle() -> SourceBundle {
    self_host_bundle_with_entry("application")
}

fn self_host_recovery_bundle() -> SourceBundle {
    self_host_bundle_with_entry("recovery_application")
}

fn self_host_bundle_with_entry(entry: &str) -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary = Segment::new(
        root.join("main.glorious").to_string_lossy(),
        format!(
            "mod frontend;\nmod probe;\n\nmain() {{ run_compiler_host(probe::scanner::{entry}) }}\n"
        ),
    );
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("probe/probe.glorious"),
        root.join("probe/scanner/scanner.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let mut source = fs::read_to_string(&path)
                .unwrap()
                .replace("pub mod lossless;\n", "")
                .replace("pub mod headers;\n", "")
                .replace("pub mod bodies;\n", "")
                .replace("pub mod resolution;\n", "")
                .replace("pub mod elaboration;\n", "");
            if path.ends_with("probe/probe.glorious") {
                source = source.replace("pub mod lexer;\n", "");
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

fn read_u32(input: &[u8], cursor: &mut usize) -> u32 {
    let end = *cursor + 4;
    let value = u32::from_le_bytes(input[*cursor..end].try_into().unwrap());
    *cursor = end;
    value
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ShellKind {
    Module = 1,
    Import = 2,
    TypeAlias = 3,
    EffectRowAlias = 4,
    Global = 5,
    Fixity = 6,
    Effect = 7,
    Struct = 8,
    Enum = 9,
    Trait = 10,
    Impl = 11,
    Function = 12,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Shell {
    kind: ShellKind,
    public: bool,
    name: Option<String>,
    header: (u32, u32),
    body: Option<(u32, u32)>,
    whole: (u32, u32),
    parent: Option<u32>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ScanError {
    code: u8,
    token: u32,
    related: u32,
}

fn ident(token: &Token, expected: &str) -> bool {
    matches!(&token.kind, TokenKind::Ident(value) if value == expected)
}

fn token_name(token: Option<&Token>) -> Option<String> {
    match token.map(|token| &token.kind) {
        Some(TokenKind::Ident(value)) => Some(value.clone()),
        _ => None,
    }
}

fn kind_and_name(
    tokens: &[Token],
    marker: usize,
    limit: usize,
    start: usize,
    sentinel: usize,
) -> Result<(ShellKind, Option<String>), ScanError> {
    let token = &tokens[marker];
    let (kind, name, name_required) = match &token.kind {
        TokenKind::Ident(value) if value == "mod" => {
            (ShellKind::Module, token_name(tokens.get(marker + 1)), true)
        }
        TokenKind::Ident(value)
            if value == "use"
                && !matches!(
                    tokens.get(marker + 1).map(|token| &token.kind),
                    Some(TokenKind::LParen | TokenKind::Lt)
                ) =>
        {
            (ShellKind::Import, token_name(tokens.get(marker + 1)), false)
        }
        TokenKind::Keyword(Kw::Type) => (
            ShellKind::TypeAlias,
            token_name(tokens.get(marker + 1)),
            true,
        ),
        TokenKind::Ident(value) if value == "cases" => (
            ShellKind::EffectRowAlias,
            token_name(tokens.get(marker + 1)),
            true,
        ),
        TokenKind::Keyword(Kw::Let) => {
            (ShellKind::Global, token_name(tokens.get(marker + 1)), true)
        }
        TokenKind::Ident(value)
            if matches!(value.as_str(), "prefix" | "infix" | "infixl" | "infixr")
                && matches!(
                    tokens.get(marker + 1).map(|token| &token.kind),
                    Some(TokenKind::Number(_))
                ) =>
        {
            (ShellKind::Fixity, token_name(tokens.get(marker + 2)), false)
        }
        TokenKind::Keyword(Kw::Effect) => {
            (ShellKind::Effect, token_name(tokens.get(marker + 1)), true)
        }
        TokenKind::Keyword(Kw::Struct) => {
            (ShellKind::Struct, token_name(tokens.get(marker + 1)), true)
        }
        TokenKind::Keyword(Kw::Enum) => (ShellKind::Enum, token_name(tokens.get(marker + 1)), true),
        TokenKind::Keyword(Kw::Trait) => {
            (ShellKind::Trait, token_name(tokens.get(marker + 1)), true)
        }
        TokenKind::Keyword(Kw::Impl) => (ShellKind::Impl, None, false),
        TokenKind::Ident(_) => (ShellKind::Function, token_name(Some(token)), true),
        _ => {
            return Err(ScanError {
                code: 4,
                token: start.try_into().unwrap(),
                related: sentinel.try_into().unwrap(),
            });
        }
    };
    if name_required && name.is_none() {
        return Err(ScanError {
            code: 6,
            token: (marker + 1).min(limit).try_into().unwrap(),
            related: start.try_into().unwrap(),
        });
    }
    Ok((kind, name))
}

fn closing_for(kind: &TokenKind) -> Option<u8> {
    match kind {
        TokenKind::LParen => Some(1),
        TokenKind::LBracket => Some(2),
        TokenKind::LBrace => Some(3),
        _ => None,
    }
}

fn closing_kind(kind: &TokenKind) -> Option<u8> {
    match kind {
        TokenKind::RParen => Some(1),
        TokenKind::RBracket => Some(2),
        TokenKind::RBrace => Some(3),
        _ => None,
    }
}

fn scan(tokens: &[Token]) -> Result<Vec<Shell>, ScanError> {
    let eof = tokens
        .iter()
        .position(|token| matches!(token.kind, TokenKind::Eof))
        .unwrap_or(tokens.len());
    let mut shells = Vec::new();
    scan_range(tokens, 0, eof, tokens.len(), None, &mut shells)?;
    Ok(shells)
}

fn scan_range(
    tokens: &[Token],
    mut cursor: usize,
    end: usize,
    eof: usize,
    parent: Option<u32>,
    shells: &mut Vec<Shell>,
) -> Result<(), ScanError> {
    while cursor < end {
        if closing_kind(&tokens[cursor].kind).is_some() {
            return Err(ScanError {
                code: 1,
                token: cursor.try_into().unwrap(),
                related: end.try_into().unwrap(),
            });
        }

        let start = cursor;
        let public = ident(&tokens[cursor], "pub");
        let marker = cursor + usize::from(public);
        if marker >= end {
            return Err(ScanError {
                code: 4,
                token: start.try_into().unwrap(),
                related: eof.try_into().unwrap(),
            });
        }
        let (kind, name) = kind_and_name(tokens, marker, end, start, eof)?;

        let semicolon_style = matches!(
            kind,
            ShellKind::Import
                | ShellKind::TypeAlias
                | ShellKind::EffectRowAlias
                | ShellKind::Global
                | ShellKind::Fixity
        );
        let mut stack = Vec::<(u8, usize)>::new();
        let mut terminator = None;
        let mut index = marker;
        while index < end {
            let token = &tokens[index].kind;
            if let Some(delimiter) = closing_for(token) {
                let function_effect_set = kind == ShellKind::Function
                    && delimiter == 3
                    && index > marker
                    && matches!(tokens[index - 1].kind, TokenKind::Slash | TokenKind::Eq);
                if delimiter == 3 && stack.is_empty() && !semicolon_style && !function_effect_set {
                    terminator = Some((index, true));
                    break;
                }
                stack.push((delimiter, index));
            } else if let Some(delimiter) = closing_kind(token) {
                let Some((expected, opening)) = stack.pop() else {
                    return Err(ScanError {
                        code: 1,
                        token: index.try_into().unwrap(),
                        related: eof.try_into().unwrap(),
                    });
                };
                if delimiter != expected {
                    return Err(ScanError {
                        code: 2,
                        token: index.try_into().unwrap(),
                        related: opening.try_into().unwrap(),
                    });
                }
            } else if matches!(token, TokenKind::Semicolon)
                && stack.is_empty()
                && (semicolon_style || kind == ShellKind::Module)
            {
                terminator = Some((index, false));
                break;
            }
            index += 1;
        }
        if let Some((_, opening)) = stack.last().copied() {
            return Err(ScanError {
                code: 3,
                token: end.try_into().unwrap(),
                related: opening.try_into().unwrap(),
            });
        }
        let Some((boundary, has_brace_body)) = terminator else {
            return Err(ScanError {
                code: 5,
                token: end.try_into().unwrap(),
                related: start.try_into().unwrap(),
            });
        };

        let (header_end, body, whole_end) = if has_brace_body {
            let close = matching_brace(tokens, boundary, end)?;
            (
                boundary,
                Some((
                    (boundary + 1).try_into().unwrap(),
                    close.try_into().unwrap(),
                )),
                close + 1,
            )
        } else if kind == ShellKind::Global {
            let initializer = top_level_equal(tokens, marker, boundary);
            match initializer {
                Some(equal) => (
                    equal + 1,
                    Some((
                        (equal + 1).try_into().unwrap(),
                        boundary.try_into().unwrap(),
                    )),
                    boundary + 1,
                ),
                None => {
                    return Err(ScanError {
                        code: 5,
                        token: boundary.try_into().unwrap(),
                        related: start.try_into().unwrap(),
                    });
                }
            }
        } else {
            (boundary + 1, None, boundary + 1)
        };

        let shell_index: u32 = shells.len().try_into().unwrap();
        shells.push(Shell {
            kind,
            public,
            name,
            header: (start.try_into().unwrap(), header_end.try_into().unwrap()),
            body,
            whole: (start.try_into().unwrap(), whole_end.try_into().unwrap()),
            parent,
        });
        if kind == ShellKind::Module
            && let Some((body_start, body_end)) = body
        {
            scan_range(
                tokens,
                body_start as usize,
                body_end as usize,
                eof,
                Some(shell_index),
                shells,
            )?;
        }
        cursor = whole_end;
    }
    Ok(())
}

fn matching_brace(tokens: &[Token], open: usize, end: usize) -> Result<usize, ScanError> {
    let mut stack = vec![(3_u8, open)];
    for (index, token) in tokens.iter().enumerate().take(end).skip(open + 1) {
        if let Some(delimiter) = closing_for(&token.kind) {
            stack.push((delimiter, index));
        } else if let Some(delimiter) = closing_kind(&token.kind) {
            let (expected, opening) = stack.pop().unwrap();
            if delimiter != expected {
                return Err(ScanError {
                    code: 2,
                    token: index.try_into().unwrap(),
                    related: opening.try_into().unwrap(),
                });
            }
            if stack.is_empty() {
                return Ok(index);
            }
        }
    }
    let (_, opening) = stack.last().copied().unwrap();
    Err(ScanError {
        code: 3,
        token: end.try_into().unwrap(),
        related: opening.try_into().unwrap(),
    })
}

fn top_level_equal(tokens: &[Token], start: usize, end: usize) -> Option<usize> {
    let mut depth = 0_usize;
    for (index, token) in tokens.iter().enumerate().take(end).skip(start) {
        match token.kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                depth = depth.saturating_sub(1);
            }
            TokenKind::Eq if depth == 0 => return Some(index),
            _ => {}
        }
    }
    None
}

fn encode_shell(output: &mut Vec<u8>, shell: &Shell) {
    output.push(shell.kind as u8);
    output.push(u8::from(shell.public));
    match &shell.name {
        Some(name) => {
            output.push(1);
            push_bytes(output, name.as_bytes());
        }
        None => output.push(0),
    }
    push_u32(output, shell.header.0);
    push_u32(output, shell.header.1);
    match shell.body {
        Some((start, end)) => {
            output.push(1);
            push_u32(output, start);
            push_u32(output, end);
        }
        None => output.push(0),
    }
    push_u32(output, shell.whole.0);
    push_u32(output, shell.whole.1);
    match shell.parent {
        Some(parent) => {
            output.push(1);
            push_u32(output, parent);
        }
        None => output.push(0),
    }
}

fn encode_rust_scan(output: &mut Vec<u8>, source: &str) {
    match grandiose::lexer::lex(source) {
        Err(_) => output.push(1),
        Ok(tokens) => match scan(&tokens) {
            Ok(shells) => {
                output.push(0);
                push_u32(output, shells.len().try_into().unwrap());
                for shell in &shells {
                    encode_shell(output, shell);
                }
            }
            Err(error) => {
                output.push(2);
                output.push(error.code);
                push_u32(output, error.token);
                push_u32(output, error.related);
            }
        },
    }
}

fn corpus(directory: &Path) -> Vec<PathBuf> {
    if CONTEXTUAL_PUB_ONLY.load(Ordering::Relaxed) {
        return vec![repository_root()
            .join("crates/grandiose/tests/fixtures/contextual_pub_headers.glorious")];
    }
    if FIXITY_ONLY.load(Ordering::Relaxed) {
        let path = directory.join("fixity.glorious");
        fs::write(
            &path,
            "infixl 10 left; infixr 20 right; infix 30 ==; infixl 40 <+>;",
        )
        .unwrap();
        return vec![path];
    }
    let focused = [
        "",
        "}",
        "mod empty;",
        "pub mod nested { type Word = u32; value() { () } }",
        "use std::prelude::*; cases Io = { Read, Write };",
        "pub type Bytes = Vec<u8>; let answer: u32 = choose(40, 2);",
        "infixl 70 +; prefix 90 !;",
        "effect Console { write(String) (); }",
        "struct Pair<T> { left: T, right: T } enum Maybe<T> { None, Some(T) }",
        "trait Show<T> { show(T) String; } impl<T> Show<T> for T { show(x: T) { x } }",
        "pub type Alias<T> = Vec<T>; cases Effects = { Console }; struct Data<T> { value: T } enum Choice<T> { Empty, Full(T) } effect Console { write(value: String) -> !; } trait Marker<T> { mark(value: T) -> (); } impl Marker<Data<u32>> for Data<u32> { mark(value: Data<u32>) { () } } impl !Marker<Choice<u32>> for Choice<u32> {} callable<T>(value: T) T { value }",
        "pub apply<T>(value: T, f: (T) U) U where { U: Use } { f(value) }",
        "apply<F, e: EffectRow>(f: F) -> () where F: Fn<(), Output=(), Effects={| e}> { f() }",
        "broken() { ([)] }",
        "mod unfinished { value() { () }",
        "let bad = \"unfinished",
    ];
    let mut paths = Vec::new();
    for (index, source) in focused.into_iter().enumerate() {
        let path = directory.join(format!("focused-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    let root = repository_root().join("self-host/src");
    paths.extend([
        root.join("main.glorious"),
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
    ]);
    paths
}

#[test]
fn self_host_scanner_contextual_pub_headers_match_bootstrap() {
    // Keep this oracle comparison on the same corpus path as the broad scanner
    // parity test so the expected wire format is always produced by the Rust
    // scanner, rather than by a hand-maintained fixture.
    CONTEXTUAL_PUB_ONLY.store(true, Ordering::Relaxed);
    self_hosted_scanner_matches_rust_in_vm_and_native_execution();
}

#[test]
fn self_host_scanner_fixity_declarations_match_bootstrap() {
    FIXITY_ONLY.store(true, Ordering::Relaxed);
    self_hosted_scanner_matches_rust_in_vm_and_native_execution();
}

#[test]
fn self_host_scanner_trait_impl_effect_shells_match_bootstrap() {
    self_hosted_scanner_matches_rust_in_vm_and_native_execution();
}

#[test]
fn self_hosted_scanner_matches_rust_in_vm_and_native_execution() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            if std::env::var_os("G1_SELF_HOST_SCANNER_CHECK_ONLY").is_some() {
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
                encode_rust_scan(&mut expected, &fs::read_to_string(path).unwrap());
            }
            fs::write(&expected_path, &expected).unwrap();

            let bundle = self_host_bundle();
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &bundle,
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
            let vm_bytes = fs::read(&vm_path).unwrap();
            if vm_bytes != expected {
                let mismatch = vm_bytes
                    .iter()
                    .zip(&expected)
                    .position(|(actual, expected)| actual != expected)
                    .unwrap_or_else(|| vm_bytes.len().min(expected.len()));
                let end = (mismatch + 16).min(vm_bytes.len().min(expected.len()));
                panic!(
                    "VM scanner diverged at byte {mismatch}: actual {:?}, expected {:?}",
                    &vm_bytes[mismatch..end],
                    &expected[mismatch..end]
                );
            }

            let executable = native_incremental::build_cached_native(
                &bundle,
                directory.path(),
                "self-host-scanner",
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
                "native whole-corpus scanner diverged"
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
                    path.display(),
                    native.status,
                    String::from_utf8_lossy(&native.stderr)
                );
                let mut expected_one = Vec::new();
                push_u32(&mut expected_one, 1);
                encode_rust_scan(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&native_path).unwrap(),
                    expected_one,
                    "native scanner diverged for input {index} ({})",
                    path.display()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_scanner_module_items_match_bootstrap() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("module.glorious");
            let source = fs::read_to_string(
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("tests/fixtures/module_frontend_conformance.glorious"),
            )
            .unwrap();
            fs::write(&input, &source).unwrap();

            let output = directory.path().join("scan.bin");
            let mut expected = Vec::new();
            push_u32(&mut expected, 1);
            encode_rust_scan(&mut expected, &source);

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm = Vm::with_host(
                verify(phases.artifact).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![
                    output.clone().into_os_string(),
                    input.into_os_string(),
                ]),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_eq!(fs::read(output).unwrap(), expected);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_unit_external_and_inline_modules_are_structural() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let source = r#"
                pub mod network;
                mod syntax {
                    pub mod tokens;
                    parse() -> i64 { 1 }
                }
                main() -> { () }
            "#;
            let tokens = grandiose::lexer::lex(source).unwrap();
            let (program, diagnostics) = parser::parse_recovering(tokens.clone());
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");

            assert_eq!(program.modules.len(), 3);
            assert_eq!(program.modules[0].name, "network");
            assert_eq!(program.modules[0].visibility, grandiose::ast::Visibility::Public);
            assert!(matches!(
                program.modules[0].kind,
                grandiose::ast::ModuleKind::External
            ));
            assert_eq!(program.modules[1].name, "syntax");
            let grandiose::ast::ModuleKind::Inline { body } = program.modules[1].kind else {
                panic!("syntax must be an inline module")
            };
            assert!(body.start < body.end);
            assert_eq!(program.modules[2].name, "tokens");
            assert_eq!(program.modules[2].visibility, grandiose::ast::Visibility::Public);
            assert!(matches!(
                program.modules[2].kind,
                grandiose::ast::ModuleKind::External
            ));
            assert!(body.start <= program.modules[2].span.start);
            assert!(program.modules[2].span.end <= body.end);
            assert_eq!(
                program
                    .functions
                    .iter()
                    .map(|function| function.name.as_str())
                    .collect::<Vec<_>>(),
                ["parse", "main"]
            );
            assert_eq!(program.visibility(program.functions[0].span), grandiose::ast::Visibility::Private);
            assert_eq!(program.visibility(program.functions[1].span), grandiose::ast::Visibility::Private);

            // Convert the AST’s source spans to the token ranges used by the
            // self-host scanner. This expected value is structural, rather
            // than a fixture of token offsets or a call to the scanner oracle.
            let token_at_start = |offset: usize| {
                tokens
                    .iter()
                    .position(|token| token.span.start == offset)
                    .unwrap()
            };
            let token_at_end = |offset: usize| {
                tokens
                    .iter()
                    .position(|token| token.span.end == offset)
                    .unwrap()
            };
            let mut expected_shells = Vec::new();
            for module in &program.modules {
                let declaration = token_at_start(module.span.start);
                let start = if module.visibility == grandiose::ast::Visibility::Public {
                    declaration - 1
                } else {
                    declaration
                };
                let end_token = token_at_end(module.span.end);
                let (header_end, body) = match module.kind {
                    grandiose::ast::ModuleKind::External => (end_token, None),
                    grandiose::ast::ModuleKind::Inline { body } => {
                        let open = token_at_end(body.start);
                        let close = token_at_start(body.end);
                        (open, Some(((open + 1) as u32, close as u32)))
                    }
                };
                let parent = program
                    .modules
                    .iter()
                    .enumerate()
                    .filter_map(|(index, owner)| match owner.kind {
                        grandiose::ast::ModuleKind::Inline { body }
                            if body.start <= module.span.start
                                && module.span.end <= body.end
                                && owner.span != module.span => Some((body.end - body.start, index)),
                        _ => None,
                    })
                    .min_by_key(|(size, _)| *size)
                    .map(|(_, index)| index as u32);
                expected_shells.push(Shell {
                    kind: ShellKind::Module,
                    public: module.visibility == grandiose::ast::Visibility::Public,
                    name: Some(module.name.clone()),
                    header: (
                        start as u32,
                        (if body.is_some() { header_end } else { header_end + 1 }) as u32,
                    ),
                    body,
                    whole: (start as u32, (end_token + 1) as u32),
                    parent,
                });
            }
            for function in &program.functions {
                let start = token_at_start(function.span.start);
                let open = token_at_start(function.body.span.start);
                let close = token_at_end(function.body.span.end);
                let parent = program
                    .modules
                    .iter()
                    .enumerate()
                    .filter_map(|(index, module)| match module.kind {
                        grandiose::ast::ModuleKind::Inline { body }
                            if body.start <= function.span.start
                                && function.span.end <= body.end => {
                                Some((body.end - body.start, index as u32))
                            }
                        _ => None,
                    })
                    .min_by_key(|(size, _)| *size)
                    .map(|(_, index)| index);
                expected_shells.push(Shell {
                    kind: ShellKind::Function,
                    public: program.visibility(function.span) == grandiose::ast::Visibility::Public,
                    name: Some(function.name.clone()),
                    header: (start as u32, open as u32),
                    body: Some(((open + 1) as u32, close as u32)),
                    whole: (start as u32, (close + 1) as u32),
                    parent,
                });
            }
            expected_shells.sort_by_key(|shell| shell.whole.0);
            let mut expected = Vec::new();
            push_u32(&mut expected, 1);
            expected.push(0);
            push_u32(&mut expected, expected_shells.len() as u32);
            for shell in &expected_shells {
                encode_shell(&mut expected, shell);
            }

            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("module-structure.glorious");
            let output = directory.path().join("module-structure.bin");
            fs::write(&input, source).unwrap();
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions { optimization_level: OptimizationLevel::O2 },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm = Vm::with_host(
                verify(phases.artifact).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_eq!(fs::read(output).unwrap(), expected);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_scanner_recovery_matches_bootstrap() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let source = "struct Good { x: i64 }\nstruct Bad { x: }\nenum Also { }\nbroken( -> { 1 }\nfine() -> i64 { 2 }";
            let tokens = grandiose::lexer::lex(source).unwrap();
            let (program, diagnostics) = parser::parse_recovering(tokens);
            assert!(diagnostics.len() >= 2, "{diagnostics:#?}");
            assert_eq!(program.structs.len(), 1);
            assert_eq!(program.structs[0].name, "Good");
            assert_eq!(program.enums.len(), 1);
            assert!(program.functions.iter().any(|function| function.name == "fine"));
            assert!(!program.functions.iter().any(|function| function.name == "broken"));

            let expected_path = tempfile::tempdir().unwrap();
            let input = expected_path.path().join("recovery.glorious");
            fs::write(&input, source).unwrap();
            let output = expected_path.path().join("expected.bin");
            let vm_output = expected_path.path().join("vm.bin");
            let native_output = expected_path.path().join("native.bin");

            let mut expected = Vec::new();
            push_u32(&mut expected, 1);
            expected.push(0);
            push_u32(&mut expected, 3);
            let shells = [
                Shell {
                    kind: ShellKind::Struct,
                    public: false,
                    name: Some("Good".into()),
                    header: (0, 2),
                    body: Some((3, 6)),
                    whole: (0, 7),
                    parent: None,
                },
                Shell {
                    kind: ShellKind::Enum,
                    public: false,
                    name: Some("Also".into()),
                    header: (13, 15),
                    body: Some((16, 16)),
                    whole: (13, 17),
                    parent: None,
                },
                Shell {
                    kind: ShellKind::Function,
                    public: false,
                    name: Some("fine".into()),
                    header: (23, 28),
                    body: Some((29, 30)),
                    whole: (23, 31),
                    parent: None,
                },
            ];
            for shell in &shells {
                encode_shell(&mut expected, shell);
            }
            push_u32(&mut expected, 2);
            expected.push(5);
            push_u32(&mut expected, 11);
            push_u32(&mut expected, 7);
            expected.push(5);
            push_u32(&mut expected, 18);
            push_u32(&mut expected, 18);
            fs::write(&output, &expected).unwrap();

            let bundle = self_host_recovery_bundle();
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &bundle,
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm_args = vec![vm_output.clone().into_os_string(), input.clone().into_os_string()];
            let vm = Vm::with_host(
                verify(phases.artifact.clone()).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vm_args),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_eq!(fs::read(&vm_output).unwrap(), expected, "VM recovery diverged");

            let executable = native_incremental::build_cached_native(
                &bundle,
                expected_path.path(),
                "recovery",
            );
            let native = Command::new(&executable)
                .arg(&native_output)
                .arg(&input)
                .output()
                .unwrap();
            assert!(
                native.status.success(),
                "native recovery status: {:?}\n{}",
                native.status,
                String::from_utf8_lossy(&native.stderr)
            );
            let mut expected_one = Vec::new();
            push_u32(&mut expected_one, 1);
            expected_one.extend_from_slice(&expected[4..]);
            assert_eq!(fs::read(&native_output).unwrap(), expected_one, "native recovery diverged");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_unit_malformed_module_and_use_items_recover() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let source = fs::read_to_string(
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("tests/fixtures/malformed-modules-and-uses.glorious"),
            )
            .unwrap();
            let tokens = grandiose::lexer::lex(&source).unwrap();
            let (program, diagnostics) = parser::parse_recovering(tokens.clone());
            assert!(diagnostics.len() >= 2, "{diagnostics:#?}");
            assert!(
                program
                    .functions
                    .iter()
                    .any(|function| function.name == "main")
            );
            let main_start = tokens
                .iter()
                .position(|token| matches!(&token.kind, grandiose::lexer::TokenKind::Ident(name) if name == "main"))
                .unwrap();
            let expected_body_start = tokens
                .iter()
                .enumerate()
                .skip(main_start)
                .find_map(|(index, token)| {
                    matches!(token.kind, grandiose::lexer::TokenKind::LBrace).then_some(index)
                })
                .unwrap();
            let expected_body_end = tokens
                .iter()
                .enumerate()
                .skip(expected_body_start + 1)
                .find_map(|(index, token)| {
                    matches!(token.kind, grandiose::lexer::TokenKind::RBrace).then_some(index)
                })
                .unwrap();

            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("malformed.glorious");
            let output = directory.path().join("recovery.bin");
            fs::write(&input, source).unwrap();

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_recovery_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm = Vm::with_host(
                verify(phases.artifact).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);

            let bytes = fs::read(output).unwrap();
            let mut cursor = 0;
            assert_eq!(read_u32(&bytes, &mut cursor), 1);
            assert_eq!(bytes[cursor], 0);
            cursor += 1;
            let shell_count = read_u32(&bytes, &mut cursor);
            assert_eq!(shell_count, 1);
            assert_eq!(bytes[cursor], ShellKind::Function as u8);
            cursor += 2; // kind and private visibility
            assert_eq!(bytes[cursor], 1);
            cursor += 1;
            let name = read_u32(&bytes, &mut cursor) as usize;
            assert_eq!(&bytes[cursor..cursor + name], b"main");
            cursor += name;
            let header_start = read_u32(&bytes, &mut cursor);
            let header_end = read_u32(&bytes, &mut cursor);
            assert!(header_start < header_end);
            assert_eq!(bytes[cursor], 1);
            cursor += 1;
            let body_start = read_u32(&bytes, &mut cursor);
            let body_end = read_u32(&bytes, &mut cursor);
            assert!(body_start < body_end);
            let whole_start = read_u32(&bytes, &mut cursor);
            let whole_end = read_u32(&bytes, &mut cursor);
            assert_eq!(
                (header_start, header_end, body_start, body_end, whole_start, whole_end),
                (
                    main_start as u32,
                    expected_body_start as u32,
                    (expected_body_start + 1) as u32,
                    expected_body_end as u32,
                    main_start as u32,
                    (expected_body_end + 1) as u32
                )
            );
            assert_eq!(bytes[cursor], 0);
            cursor += 1;
            let error_count = read_u32(&bytes, &mut cursor);
            assert_eq!(error_count, diagnostics.len() as u32);
            let mut error_codes = Vec::new();
            for _ in 0..error_count {
                error_codes.push(bytes[cursor]);
                cursor += 1;
                let token = read_u32(&bytes, &mut cursor);
                let related = read_u32(&bytes, &mut cursor);
                assert!((token as usize) < tokens.len());
                assert!((related as usize) <= tokens.len());
            }
            assert_eq!(error_codes, [5, 5, 4]);
            assert_eq!(cursor, bytes.len());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_scanner_use_trees_match_bootstrap() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let input = repository_root().join("crates/grandiose/tests/fixtures/use_trees.glorious");
            let source = fs::read_to_string(&input).unwrap();
            let output = directory.path().join("scanner.bin");
            let mut expected = Vec::new();
            push_u32(&mut expected, 1);
            encode_rust_scan(&mut expected, &source);

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm_args = vec![output.clone().into_os_string(), input.into_os_string()];
            let vm = Vm::with_host(
                verify(phases.artifact).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vm_args),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_eq!(fs::read(output).unwrap(), expected);
        })
        .unwrap()
        .join()
        .unwrap();
}
