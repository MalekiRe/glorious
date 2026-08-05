use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    CompileOptions, LlvmOptions, OptimizationLevel,
    lossless::{LosslessKind, lex_lossless},
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
        "mod frontend;\nmod probe;\n\nmain() { run_compiler_host(probe::lossless::application) }\n",
    );
    let frontend = fs::read_to_string(root.join("frontend/frontend.glorious"))
        .unwrap()
        .replace("pub mod scanner;\n", "")
        .replace("pub mod headers;\n", "")
        .replace("pub mod bodies;\n", "")
        .replace("pub mod resolution;\n", "")
        .replace("pub mod elaboration;\n", "");
    let probe = fs::read_to_string(root.join("probe/probe.glorious"))
        .unwrap()
        .replace("pub mod lexer;\n", "")
        .replace("pub mod scanner;\n", "")
        .replace("pub mod headers;\n", "")
        .replace("pub mod bodies;\n", "")
        .replace("pub mod resolution;\n", "")
        .replace("pub mod elaboration;\n", "");
    SourceBundle::distributed(
        primary,
        [
            Segment::new(
                root.join("frontend/frontend.glorious").to_string_lossy(),
                frontend,
            ),
            Segment::new(
                root.join("frontend/lexer/lexer.glorious").to_string_lossy(),
                fs::read_to_string(root.join("frontend/lexer/lexer.glorious")).unwrap(),
            ),
            Segment::new(
                root.join("frontend/lossless/lossless.glorious")
                    .to_string_lossy(),
                fs::read_to_string(root.join("frontend/lossless/lossless.glorious")).unwrap(),
            ),
            Segment::new(root.join("probe/probe.glorious").to_string_lossy(), probe),
            Segment::new(
                root.join("probe/lossless/lossless.glorious")
                    .to_string_lossy(),
                fs::read_to_string(root.join("probe/lossless/lossless.glorious")).unwrap(),
            ),
        ],
    )
}

fn kind_code(kind: LosslessKind) -> u8 {
    match kind {
        LosslessKind::Whitespace => 1,
        LosslessKind::LineComment => 2,
        LosslessKind::BlockComment => 3,
        LosslessKind::Identifier => 4,
        LosslessKind::Number => 5,
        LosslessKind::String => 6,
        LosslessKind::Character => 7,
        LosslessKind::ByteString => 8,
        LosslessKind::ByteCharacter => 9,
        LosslessKind::Lifetime => 10,
        LosslessKind::Label => 11,
        LosslessKind::Punctuation => 12,
    }
}

fn error_code(title: &str) -> u8 {
    match title {
        "unfinished comment" => 1,
        "unfinished string" => 2,
        "unfinished byte string" => 3,
        "unfinished byte literal" => 4,
        "unfinished character literal" => 5,
        "invalid lifetime identifier" => 6,
        other => panic!("unmapped lossless error title `{other}`"),
    }
}

fn push_u32(output: &mut Vec<u8>, value: u32) {
    output.extend(value.to_le_bytes());
}

fn push_u64(output: &mut Vec<u8>, value: u64) {
    output.extend(value.to_le_bytes());
}

fn encode_rust(output: &mut Vec<u8>, source: &str) {
    match lex_lossless(source) {
        Ok(tokens) => {
            output.push(0);
            push_u32(output, tokens.len().try_into().unwrap());
            for token in tokens {
                output.push(kind_code(token.kind));
                output.push(u8::from(token.kind.is_trivia()));
                output.push(u8::from(token.kind.is_comment()));
                push_u64(output, token.span.start as u64);
                push_u64(output, token.span.end as u64);
            }
        }
        Err(error) => {
            output.push(1);
            output.push(error_code(&error.title));
            let span = error.span.unwrap();
            push_u64(output, span.start as u64);
            push_u64(output, span.end as u64);
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RawToken {
    kind: u8,
    trivia: bool,
    comment: bool,
    start: usize,
    end: usize,
}

#[derive(Debug, Eq, PartialEq)]
enum RawResult {
    Tokens(Vec<RawToken>),
    Error { kind: u8, start: usize, end: usize },
}

struct Decoder<'a> {
    bytes: &'a [u8],
    cursor: usize,
}

impl Decoder<'_> {
    fn byte(&mut self) -> u8 {
        let value = self.bytes[self.cursor];
        self.cursor += 1;
        value
    }

    fn u32(&mut self) -> u32 {
        let bytes = self.bytes[self.cursor..self.cursor + 4].try_into().unwrap();
        self.cursor += 4;
        u32::from_le_bytes(bytes)
    }

    fn usize(&mut self) -> usize {
        let bytes = self.bytes[self.cursor..self.cursor + 8].try_into().unwrap();
        self.cursor += 8;
        u64::from_le_bytes(bytes).try_into().unwrap()
    }
}

fn decode(bytes: &[u8]) -> Vec<RawResult> {
    let mut decoder = Decoder { bytes, cursor: 0 };
    let count = decoder.u32();
    let mut results = Vec::new();
    for _ in 0..count {
        match decoder.byte() {
            0 => {
                let count = decoder.u32();
                let mut tokens = Vec::new();
                for _ in 0..count {
                    tokens.push(RawToken {
                        kind: decoder.byte(),
                        trivia: decoder.byte() != 0,
                        comment: decoder.byte() != 0,
                        start: decoder.usize(),
                        end: decoder.usize(),
                    });
                }
                results.push(RawResult::Tokens(tokens));
            }
            1 => results.push(RawResult::Error {
                kind: decoder.byte(),
                start: decoder.usize(),
                end: decoder.usize(),
            }),
            tag => panic!("unexpected lossless result tag {tag}"),
        }
    }
    assert_eq!(decoder.cursor, bytes.len());
    results
}

fn fixtures() -> Vec<&'static str> {
    vec![
        "\n// docs 😀\nmain() -> f64 { /* one /* two */ three */ 1.25e-3 }\n",
        "b\"raw\\xff\" 'life 'λ' '\\u{1F600}' @label 0xffff_ffff +-*\n",
        "a/* outer /* inner */ end */ // tail\nb",
        "prefix /* open",
        "prefix \"open",
        "prefix b\"open",
        "// 😀\nvalue + 'λ'",
    ]
}

fn assert_round_trip(source: &str, tokens: &[RawToken]) {
    let mut cursor = 0;
    let mut reconstructed = String::new();
    for token in tokens {
        assert_eq!(token.start, cursor);
        assert!(token.end > token.start);
        reconstructed.push_str(&source[token.start..token.end]);
        cursor = token.end;
    }
    assert_eq!(cursor, source.len());
    assert_eq!(reconstructed, source);
}

fn assert_bootstrap_cases(encoded: &[u8]) {
    let sources = fixtures();
    let results = decode(encoded);
    assert_eq!(results.len(), sources.len());

    for index in [0, 1, 2, 6] {
        let RawResult::Tokens(tokens) = &results[index] else {
            panic!("fixture {index} unexpectedly failed")
        };
        assert_round_trip(sources[index], tokens);
    }

    let RawResult::Tokens(comments) = &results[2] else {
        unreachable!()
    };
    let comments = comments
        .iter()
        .filter(|token| token.comment)
        .collect::<Vec<_>>();
    assert_eq!(comments.len(), 2);
    assert_eq!(comments[0].kind, 3);
    assert!(comments[0].trivia);
    assert_eq!(
        &sources[2][comments[0].start..comments[0].end],
        "/* outer /* inner */ end */"
    );
    assert_eq!(comments[1].kind, 2);
    assert!(comments[1].trivia);
    assert_eq!(&sources[2][comments[1].start..comments[1].end], "// tail");

    for (index, kind) in [(3, 1), (4, 2), (5, 3)] {
        assert_eq!(
            results[index],
            RawResult::Error {
                kind,
                start: 7,
                end: sources[index].len(),
            }
        );
    }

    let RawResult::Tokens(multibyte) = &results[6] else {
        unreachable!()
    };
    let value = multibyte
        .iter()
        .find(|token| &sources[6][token.start..token.end] == "value")
        .unwrap();
    assert_eq!(value.start, 8);
    assert_eq!(sources[6][..value.start].encode_utf16().count(), 6);
}

#[test]
fn self_hosted_lossless_lexer_covers_bootstrap_contract_in_vm_and_native() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let sources = fixtures();
            let paths = sources
                .iter()
                .enumerate()
                .map(|(index, source)| {
                    let path = directory.path().join(format!("lossless-{index}.glorious"));
                    fs::write(&path, source).unwrap();
                    path
                })
                .collect::<Vec<_>>();
            let mut expected = Vec::new();
            push_u32(&mut expected, sources.len().try_into().unwrap());
            for source in &sources {
                encode_rust(&mut expected, source);
            }
            assert_bootstrap_cases(&expected);

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();

            let vm_path = directory.path().join("vm.bin");
            let vm_args = std::iter::once(vm_path.clone().into_os_string())
                .chain(paths.iter().map(|path| path.clone().into_os_string()))
                .collect::<Vec<OsString>>();
            let vm = Vm::with_host(
                verify(phases.artifact.clone()).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vm_args),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            let vm_output = fs::read(vm_path).unwrap();
            assert_eq!(vm_output, expected, "VM lossless lexer diverged");
            assert_bootstrap_cases(&vm_output);

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-lossless.ll");
            let executable = directory.path().join("self-host-lossless");
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

            let native_path = directory.path().join("native.bin");
            let native = Command::new(&executable)
                .arg(&native_path)
                .args(&paths)
                .output()
                .unwrap();
            assert!(
                native.status.success(),
                "{}",
                String::from_utf8_lossy(&native.stderr)
            );
            let native_output = fs::read(native_path).unwrap();
            assert_eq!(native_output, expected, "native lossless lexer diverged");
            assert_bootstrap_cases(&native_output);
        })
        .unwrap()
        .join()
        .unwrap();
}
