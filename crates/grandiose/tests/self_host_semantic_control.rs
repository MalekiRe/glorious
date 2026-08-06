use std::{fs, path::{Path, PathBuf}};
use grandiose::{CompileOptions, compile_source_to_phases_with_options, source_bundle::{Segment, SourceBundle}};
use grandiose_vm::{SystemHost, Value, Vm, verify};

fn root() -> PathBuf { Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap().to_owned() }
fn bundle() -> SourceBundle {
    let r = root().join("self-host/src");
    let main = Segment::new(r.join("main.glorious").to_string_lossy(), "mod frontend; mod probe; main() { run_compiler_host(probe::elaboration::application) }" );
    let paths = ["frontend/frontend.glorious","frontend/lexer/lexer.glorious","frontend/scanner/scanner.glorious","frontend/headers/headers.glorious","frontend/bodies/bodies.glorious","frontend/resolution/resolution.glorious","frontend/elaboration/elaboration.glorious","probe/probe.glorious","probe/elaboration/elaboration.glorious"];
    SourceBundle::distributed(main, paths.into_iter().map(|p| {
        let path=r.join(p); let mut s=fs::read_to_string(&path).unwrap().replace("pub mod lossless;\n", "");
        if p=="probe/probe.glorious" { for m in ["lexer","scanner","headers","bodies","resolution"] { s=s.replace(&format!("pub mod {m};\n"), ""); } }
        Segment::new(path.to_string_lossy(),s)
    }))
}

#[test]
fn self_host_semantic_control_acceptance_and_rejection_match_rust_oracle() {
    let corpus = [
        "answer() -> i64 { @answer(42) } main() { () }",
        "enum Choice { Yes(i64), No } answer() -> Bool { Choice::Yes(1) is Choice::Yes(_) } main() { () }",
        "answer() -> i64 { let f = (x: i64) -> i64 { x + 1 }; f(41) } main() { () }",
        "answer() -> i64 { @missing(1) } main() { () }",
        "enum Choice { Yes(i64), No } answer() -> Bool { Choice::Yes(1) is Choice::Maybe } main() { () }",
    ];
    let dir=tempfile::tempdir().unwrap(); let mut paths=Vec::new(); let mut expected=Vec::new();
    for (i, source) in corpus.iter().enumerate() { let name = format!("{i}.glorious"); let path=dir.path().join(&name); fs::write(&path,source).unwrap(); paths.push(path); expected.push(compile_source_to_phases_with_options(&name,source,CompileOptions::default()).is_ok()); }
    let phases=grandiose::compile_bundle_to_phases_with_options(&bundle(),CompileOptions::default()).unwrap();
    let entry=phases.artifact.entry_function.unwrap();
    for (i, (path, ok)) in paths.into_iter().zip(expected).enumerate() {
        let output=dir.path().join(format!("out-{i}.bin"));
        let args=vec![output.clone().into_os_string(),path.into_os_string()];
        let vm=Vm::with_host(verify(phases.artifact.clone()).unwrap(),["process.args","fs.read","fs.write","diagnostic"],SystemHost::new(args)).unwrap();
        assert_eq!(vm.run(entry,vec![]).unwrap(),Value::Unit);
        let bytes=fs::read(output).unwrap();
        assert_eq!(u32::from_le_bytes(bytes[..4].try_into().unwrap()),1);
        assert_eq!(bytes[4]==0,ok,"semantic status diverged for corpus case {i}");
    }
}
