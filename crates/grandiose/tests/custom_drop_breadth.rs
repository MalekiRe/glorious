use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::verify;

const LEVELS: [OptimizationLevel; 4] = [
    OptimizationLevel::O0,
    OptimizationLevel::O1,
    OptimizationLevel::O2,
    OptimizationLevel::O3,
];

fn compile_at(source: &str, level: OptimizationLevel) -> Result<(), Vec<String>> {
    compile_source_to_phases_with_options(
        "custom-drop-breadth.gr",
        source,
        CompileOptions {
            optimization_level: level,
        },
    )
    .map_err(|diagnostics| {
        diagnostics
            .into_iter()
            .map(|diagnostic| diagnostic.message)
            .collect()
    })
    .and_then(|phases| {
        verify(phases.artifact)
            .map(|_| ())
            .map_err(|error| vec![error.to_string()])
    })
}

#[test]
fn pure_drop_bodies_support_locals_aggregates_calls_enums_and_ground_generics_o0_o3() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        enum Flag { On, Off }
        struct Resource { marker: i64, flag: Flag }

        grounded<T>(value: T) -> T { value }
        increment(value: i64) -> i64 { value + 1 }

        impl Drop for Resource {
            drop(&mut self) -> {
                let copied = self.marker;
                let computed = increment(copied);
                let pair = Pair { left: computed, right: grounded(2) };
                if(self.flag is Flag::On) {
                    pair.left;
                    ()
                } else {
                    pair.right;
                    ()
                }
            }
        }

        consume(value: Resource) -> () { () }
        main() -> () { consume(Resource { marker: 40, flag: Flag::On }); () }
    "#;

    for level in LEVELS {
        compile_at(source, level).unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"));
    }
}

#[test]
fn aggregate_construction_does_not_hide_forbidden_drop_operations_o0_o3() {
    let cases = [
        (
            "move-self",
            r#"
                struct Resource { marker: i64 }
                struct Envelope { resource: &mut Resource }
                impl Drop for Resource {
                    drop(&mut self) -> { let hidden = Envelope { resource: self }; () }
                }
                main() -> () { () }
            "#,
            "moving or exposing Drop::drop self",
        ),
        (
            "partial-move",
            r#"
                struct Payload { value: i64 }
                impl Use<[0,1]> for Payload {}
                struct Resource { payload: Payload }
                struct Envelope { payload: Payload }
                impl Drop for Resource {
                    drop(&mut self) -> { let hidden = Envelope { payload: self.payload }; () }
                }
                main() -> () { () }
            "#,
            "moving a field from Drop::drop",
        ),
        (
            "effect",
            r#"
                effect Stop { stop() -> ! }
                struct UnitBox { value: () }
                struct Resource { marker: i64 }
                effectful() -> () / {Stop} { perform Stop::stop() }
                impl Drop for Resource {
                    drop(&mut self) -> { let hidden = UnitBox { value: effectful() }; () }
                }
                main() -> () { () }
            "#,
            "synchronously without outward effects",
        ),
        (
            "indirect",
            r#"
                struct UnitBox { value: () }
                struct Resource { marker: i64 }
                impl Drop for Resource {
                    drop(&mut self) -> {
                        let callable = (value: i64) -> i64 { value };
                        let hidden = UnitBox { value: { callable(1); () } };
                        ()
                    }
                }
                main() -> () { () }
            "#,
            "first-class callable in Drop::drop",
        ),
        (
            "invalidating-mutation",
            r#"
                struct UnitBox { value: () }
                struct Resource { marker: i64 }
                impl Drop for Resource {
                    drop(&mut self) -> {
                        (*self).marker = 1;
                        let hidden = UnitBox { value: () };
                        ()
                    }
                }
                main() -> () { () }
            "#,
            "custom Drop hook",
        ),
        (
            "closed-suspension",
            r#"
                effect Ask { [1,1] ask() -> i64 }
                struct NumberBox { value: i64 }
                struct Resource { marker: i64 }
                closed() -> i64 {
                    handle { perform Ask::ask() } {
                        Ask::ask() with continuation => resume(continuation, 1)
                    }
                }
                relay() -> i64 { closed() }
                impl Drop for Resource {
                    drop(&mut self) -> { let hidden = NumberBox { value: relay() }; () }
                }
                main() -> () { () }
            "#,
            "effectful call from Drop::drop",
        ),
    ];

    for level in LEVELS {
        for (name, source, expected) in cases {
            let errors = compile_at(source, level)
                .expect_err(&format!("{level:?} {name} unexpectedly compiled"));
            assert!(
                errors.iter().any(|message| message.contains(expected)),
                "{level:?} {name}: expected {expected:?}, got {errors:#?}",
            );
        }
    }
}
