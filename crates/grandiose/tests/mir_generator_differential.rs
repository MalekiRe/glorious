use grandiose::{
    CompileOptions, OptimizationLevel, OptimizationPass, compile_source_to_phases_with_options,
};
use grandiose_vm::{Value, Vm, verify};

fn generated_source(seed: u64) -> String {
    let left = (seed & 0x3ff) as i64;
    let right = ((seed >> 10) & 0x3ff) as i64;
    format!(
        r#"
        struct Pair {{ left: i64, right: i64 }}
        effect Select {{ select(value: Pair) -> ! }}
        consume(pair: Pair) -> i64 {{
            let Pair {{ left, right }} = move pair;
            let view = &left;
            *view + right
        }}
        answer() -> i64 {{
            let total = consume(handle perform Select::select(Pair {{ left: {left}, right: {right} }}) {{
                Select::select(pair) => move pair
            }});
            move total
        }}
        main() -> () {{ answer(); () }}
        "#
    )
}

fn run(seed: u64, level: OptimizationLevel) -> (Value, Vec<OptimizationPass>) {
    let phases = compile_source_to_phases_with_options(
        "generated-mir.glorious",
        &generated_source(seed),
        CompileOptions {
            optimization_level: level,
        },
    )
    .unwrap_or_else(|errors| panic!("seed {seed:#x} {level:?}: {errors:#?}"));
    let function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .expect("generated answer function") as u32;
    let value = Vm::new(verify(phases.artifact).unwrap())
        .run(function, vec![])
        .unwrap();
    let passes = phases
        .optimization_report
        .passes
        .into_iter()
        .map(|report| report.pass)
        .collect();
    (value, passes)
}

#[test]
fn reproducible_generated_ownership_and_effect_cases_are_vm_differential() {
    // Each seed is a complete shrink key: reducing the seed reduces only the
    // two payload constants while preserving the ownership/effect CFG shape.
    for seed in [0, 0x5eed, u32::MAX as u64] {
        let baseline = run(seed, OptimizationLevel::O0).0;
        let mut optimized = None;
        for level in [
            OptimizationLevel::O1,
            OptimizationLevel::O2,
            OptimizationLevel::O3,
        ] {
            let observed = run(seed, level);
            assert_eq!(observed.0, baseline, "seed {seed:#x} {level:?}");
            if level == OptimizationLevel::O3 {
                optimized = Some(observed);
            }
        }
        let first = optimized.unwrap();
        if seed == 0 {
            let second = run(seed, OptimizationLevel::O3);
            assert_eq!(first, second, "seed {seed:#x} must be deterministic");
        }
        for mandatory in [
            OptimizationPass::ValidateRawMir,
            OptimizationPass::ImportAndValidatePlaceFlow,
            OptimizationPass::ElaborateCleanup,
            OptimizationPass::ValidateCleanupMir,
            OptimizationPass::NormalizeCfg,
            OptimizationPass::SparseSimplify,
            OptimizationPass::GlobalSimplify,
            OptimizationPass::EraseLoanProofsAndScalarizedReferences,
            OptimizationPass::ValidateBytecodeInput,
            OptimizationPass::LowerRegistersAndEdges,
            OptimizationPass::LayoutAndPeephole,
            OptimizationPass::ValidateFinalArtifact,
        ] {
            assert!(
                first.1.contains(&mandatory),
                "seed {seed:#x} did not exercise {mandatory:?}: {:?}",
                first.1
            );
        }
    }
}
