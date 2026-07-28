use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::verify;

#[test]
fn deeply_nested_generic_arguments_have_linear_discovery_work() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            // `obvious_argument_type` examines nested generic arguments before
            // the ordinary expression walk. Keep this depth high enough that
            // visiting every child once is trivial while visiting it once per
            // defaulting pass at every level is infeasible.
            let nested = (0..48).fold(String::from("42"), |value, _| {
                format!("scaling_identity({value})")
            });
            let source = format!(
                r#"
                    scaling_identity<T>(value: T) -> T {{ move value }}
                    scaling_discard<T>(value: T) -> () where T: Use<[0,0]> {{
                        value;
                        ()
                    }}
                    exercise() -> () {{
                        scaling_discard({nested})
                    }}
                    main() -> () {{ () }}
                "#
            );

            let phases = compile_source_to_phases_with_options(
                "nested-specialization-discovery.glorious",
                &source,
                CompileOptions {
                    optimization_level: OptimizationLevel::O0,
                },
            )
            .unwrap_or_else(|errors| panic!("{errors:#?}"));
            verify(phases.artifact).unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
}
