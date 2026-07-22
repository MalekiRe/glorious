use grandiose::compiler_mir::OptimizationLevel;
use grandiose::{CompileOptions, compile_source_to_phases, compile_source_to_phases_with_options};
use grandiose_vm::{Artifact, Value, Vm, verify};

const LEVELS: [OptimizationLevel; 3] = [
    OptimizationLevel::O1,
    OptimizationLevel::O2,
    OptimizationLevel::O3,
];

fn mixed_replay_source(use_interval: &str) -> String {
    format!(
        r#"
            effect Duo {{ stop() -> ! [2,2] choose() -> i64 }}
            struct Ticket {{ marker: i64 }}
            impl Use<{use_interval}> for Ticket {{}}
            consume(ticket: Ticket) -> i64 {{
                let Ticket {{ marker }} = ticket;
                marker + 2
            }}

            run() -> i64 {{
                let ticket = Ticket {{ marker: 20 }};
                handle {{
                    let selected = perform Duo::choose();
                    perform Duo::stop()
                }} {{
                    Duo::choose() with k => {{
                        let ignored = resume(k, 1);
                        resume(move k, 2)
                    }}
                    Duo::stop() => consume(move ticket)
                }}
            }}
            main() -> {{ () }}
        "#
    )
}

#[test]
fn affine_capture_is_rejected_when_terminal_consumption_can_be_replayed_twice() {
    let errors = compile_source_to_phases(
        "shared-handler-affine-replay.glorious",
        &mixed_replay_source("[0,1]"),
    )
    .expect_err("an affine owner cannot be consumed in two continuation replays");
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G1HE003")
                && error.message.contains("`ticket`")
                && error.message.contains("2 continuation replay")
                && error.message.contains("[0,1]")
        }),
        "{errors:#?}"
    );
}

#[test]
fn exact_two_use_capture_matches_two_terminal_replays() {
    for level in LEVELS {
        let phases = compile_source_to_phases_with_options(
            "shared-handler-exact-replay.glorious",
            &mixed_replay_source("[2,2]"),
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap_or_else(|errors| {
            panic!("{level:?}: replay-compatible capture was rejected: {errors:#?}")
        });
        let encoded = phases.artifact.encode();
        let artifact = Artifact::decode(&encoded).expect("artifact decodes");
        assert_eq!(
            artifact.encode(),
            encoded,
            "{level:?}: canonical codec round trip"
        );
        let verified = verify(artifact).expect("artifact verifies");
        let run = verified
            .artifact()
            .functions
            .iter()
            .position(|function| function.name == "run")
            .expect("run is emitted") as u32;
        assert_eq!(
            Vm::new(verified).run(run, vec![]).unwrap(),
            Value::I64(22),
            "{level:?}"
        );
    }
}
