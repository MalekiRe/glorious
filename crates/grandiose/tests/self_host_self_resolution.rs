// Focused Self-resolution + trait/impl interface-collection parity gate.
//
// The self-host elaboration frontend must collect trait and impl method
// signatures whose types reference the implicit `Self` subject (Rust binder
// model: `Self` resolves at index = explicit_generics_count of the enclosing
// trait, and for an impl it resolves to the implementation's self type).
// Previously `collect_interfaces` raised `UnknownTypeName` for `Self`, which
// stopped the self-host compiler at interface collection on any trait-bearing
// source (the stdlib prelude defines `trait Eq`/`trait Add` etc.).
//
// This test is deliberately scoped to the interface-collection boundary: for
// every corpus source the Rust oracle must ACCEPT it end-to-end, and the
// self-host frontend must advance past interface collection (status 0). It
// therefore pins the foundational Self-resolution increment without coupling
// to body elaboration / lowering of trait bodies (a separate milestone).
use std::{fs, path::{Path, PathBuf}};
use grandiose::{
    CompileOptions, OptimizationLevel, compile_bundle_to_phases_with_options,
    compile_source_to_bytecode, source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{SystemHost, Value, Vm, verify};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap().to_owned()
}

fn self_host_bundle() -> SourceBundle {
    let r = root().join("self-host/src");
    let main = Segment::new(
        r.join("main.glorious").to_string_lossy(),
        "mod frontend;\nmod probe;\n\nmain() { run_compiler_host(probe::elaboration::application) }\n",
    );
    let paths = [
        "frontend/frontend.glorious", "frontend/lexer/lexer.glorious",
        "frontend/scanner/scanner.glorious", "frontend/headers/headers.glorious",
        "frontend/bodies/bodies.glorious", "frontend/resolution/resolution.glorious",
        "frontend/elaboration/elaboration.glorious",
        "probe/probe.glorious", "probe/elaboration/elaboration.glorious",
    ];
    SourceBundle::distributed(main, paths.into_iter().map(|p| {
        let path = r.join(p);
        let mut s = fs::read_to_string(&path).unwrap().replace("pub mod lossless;\n", "");
        if p == "probe/probe.glorious" {
            for m in ["lexer", "scanner", "headers", "bodies", "resolution"] {
                s = s.replace(&format!("pub mod {m};\n"), "");
            }
        }
        Segment::new(path.to_string_lossy(), s)
    }))
}

fn artifact_function_id(artifact: &grandiose_vm::Artifact, suffix: &str) -> u32 {
    artifact.functions.iter()
        .position(|f| f.name.ends_with(suffix))
        .unwrap_or_else(|| panic!("self-host probe is missing `{suffix}`")) as u32
}

fn self_host_collect_status(
    function: u32, verified: &grandiose_vm::VerifiedArtifact, source: &str,
) -> u64 {
    let vm = Vm::with_host(
        verified.clone(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(Vec::<std::ffi::OsString>::new()),
    )
    .unwrap();
    let Value::U64(status) = vm.run(function, vec![Value::Text(source.to_owned().into())]).unwrap()
    else {
        panic!("interface_collection_status did not return u64");
    };
    status
}

#[test]
fn self_host_interface_collection_resolves_trait_and_impl_self() {
    let phases = compile_bundle_to_phases_with_options(&self_host_bundle(), CompileOptions {
        optimization_level: OptimizationLevel::O2,
    }).unwrap();
    let function = artifact_function_id(&phases.artifact, ":interface_collection_status");
    let verified = verify(phases.artifact.clone()).unwrap();
    drop(phases);

    let corpus = [
        // Oracle + self-host both accept: no traits.
        "pipeline_identity(value: i64) -> i64 { value } main() { () }",
        // Trait `Self` in a shared-reference receiver (Eq-style).
        "trait Greetable { greet(self: &Self); } main() { () }",
        // Trait `Self` used by-value and as the result type (Add-style).
        "trait AdderT { add(self: Self, other: Self) -> Self; } main() { () }",
        // Trait `Self` as a bare result with no self receiver (Default-style).
        "trait Defaulted { default() -> Self; } main() { () }",
        // Generic trait: `Self` binds at index = explicit_generics_count
        // (T is 0, Self is 1) in the Rust binder model.
        "trait Tag<T> { tag(self: Self) -> Self; } main() { () }",
        // Trait `Self` + a concrete impl; impl method uses the concrete self ty.
        "trait Greetable { greet(self: &Self); } impl Greetable for u8 { greet(self: &u8) { } } main() { () }",
        // Impl with a `Self`-typed method (impl Self resolves to the self type).
        "trait AdderT { add(self: Self, other: Self) -> Self; } impl AdderT for u8 { add(self: u8, other: u8) -> u8 { other } } main() { () }",
    ];

    for (index, source) in corpus.iter().enumerate() {
        let oracle_accepted = compile_source_to_bytecode("self-resolution.glorious", source).is_ok();
        assert!(oracle_accepted, "Rust oracle must accept corpus case {index}: {source}");
        let status = self_host_collect_status(function, &verified, source);
        assert_eq!(
            status, 0,
            "self-host interface collection must advance past `Self` for corpus case {index}: {source:?} (phase {status})"
        );
    }
}
