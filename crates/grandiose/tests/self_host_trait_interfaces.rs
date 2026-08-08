// Trait/impl (instance) arena + where-clause goal collection parity gate.
//
// The self-host elaboration frontend must build the trait/impl instance arena
// during interface collection: one entry per `trait` declaration (with its
// generic scope, method callable range, and constraint clause) and one entry
// per `impl` (a concrete trait instance: resolved self type, implemented trait
// name, its own where-clause goals, and method callable range).
//
// This gate is scoped to the interface-collection boundary (mirroring
// self_host_self_resolution): for each corpus source the Rust oracle must
// accept it end-to-end, and the self-host frontend must advance past interface
// collection (status 0) while populating the trait/impl arena and collecting
// where-clause goals. Body elaboration / lowering of trait bodies remains a
// separate milestone.
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

fn self_host_trait_impl_metadata(
    function: u32, verified: &grandiose_vm::VerifiedArtifact, source: &str,
) -> (u32, u32, u32, u32) {
    let vm = Vm::with_host(
        verified.clone(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(Vec::<std::ffi::OsString>::new()),
    )
    .unwrap();
    let Value::Aggregate(aggregate) = vm.run(function, vec![Value::Text(source.to_owned().into())]).unwrap()
    else {
        panic!("trait_impl_metadata did not return an aggregate tuple");
    };
    let borrowed = aggregate.borrow();
    let mut fields = borrowed.fields.iter().cloned();
    let mut next = |what: &str| -> u32 {
        let Value::U64(v) = fields.next().unwrap().unwrap() else {
            panic!("metadata {what} not u64");
        };
        v as u32
    };
    (next("status"), next("traits"), next("impls"), next("goals"))
}

#[test]
fn self_host_trait_impl_arena_and_where_clause_goals() {
    let phases = compile_bundle_to_phases_with_options(&self_host_bundle(), CompileOptions {
        optimization_level: OptimizationLevel::O2,
    }).unwrap();
    let function = artifact_function_id(&phases.artifact, ":trait_impl_metadata");
    let verified = verify(phases.artifact.clone()).unwrap();
    drop(phases);

    // (source, expected (traits, impls, goals_min))
    let corpus: &[(&str, (u32, u32, u32))] = &[
        // No trait or impl declarations: empty arenas.
        ("pipeline_identity(value: i64) -> i64 { value } main() { () }", (0, 0, 0)),
        // A bare trait with one method: one trait arena entry, no impls.
        ("trait Greetable { greet(self: &Self); } main() { () }", (1, 0, 0)),
        // Trait plus a concrete impl; the impl self type resolves and the where
        // clause (empty here) produces no goals.
        ("trait Greetable { greet(self: &Self); } impl Greetable for u8 { greet(self: &u8) { } } main() { () }", (1, 1, 0)),
        // Trait with a self-typed impl; the impl method resolves `Self` to the
        // concrete self type.
        ("trait AdderT { add(self: Self, other: Self) -> Self; } impl AdderT for u8 { add(self: u8, other: u8) -> u8 { other } } main() { () }", (1, 1, 0)),
        // Two non-generic traits with a concrete impl carrying a non-empty
        // where clause: where-clause goal collection must populate the impl
        // arena entry with the `u8: B2` goal.
        ("trait B2{} trait A2{} impl B2 for u8{} impl A2 for u8 where u8:B2{} main() { () }", (2, 2, 1)),
    ];

    for (index, (source, (traits, impls, goals_min))) in corpus.iter().enumerate() {
        let oracle_accepted = compile_source_to_bytecode("trait-impl.glorious", source).is_ok();
        assert!(oracle_accepted, "Rust oracle must accept corpus case {index}: {source}");
        let (status, got_traits, got_impls, got_goals) =
            self_host_trait_impl_metadata(function, &verified, source);
        assert_eq!(status, 0, "self-host must advance past interface collection for corpus case {index}: {source:?}");
        assert_eq!(got_traits, *traits, "trait count mismatch for corpus case {index}: {source:?}");
        assert_eq!(got_impls, *impls, "impl count mismatch for corpus case {index}: {source:?}");
        assert!(
            got_goals >= *goals_min,
            "where-clause goal collection mismatch for corpus case {index}: {source:?} (goals {got_goals} < {goals_min})"
        );
    }
}
