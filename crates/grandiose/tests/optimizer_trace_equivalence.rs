//! O0 is the semantic oracle for observable control/host traces. Optimized
//! programs must preserve ordering across perform, resume, cancel, leave, and
//! the compiler-host boundary—not merely return the same final value.

use std::sync::{Arc, Mutex};

use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Host, HostFault, Value, Vm, verify};

const SOURCE: &str = r#"
    effect Probe { [0,1] probe(message: String) -> () }

    resumed() -> () / {Diagnostic} {
        write_diagnostic("resume:before");
        handle perform Probe::probe("resume:perform") {
            Probe::probe(message) with continuation => {
                write_diagnostic(move message);
                resume(move continuation, ())
            },
        };
        write_diagnostic("resume:after");
        ()
    }

    cancelled() -> () / {Diagnostic} {
        write_diagnostic("cancel:before");
        handle perform Probe::probe("cancel:perform") {
            Probe::probe(message) with continuation => {
                write_diagnostic(move message);
                cancel(move continuation)
            },
        };
        write_diagnostic("cancel:after");
        ()
    }

    left() -> () / {Diagnostic} {
        write_diagnostic("leave:before");
        label @done: {
            write_diagnostic("leave:inside");
            leave@done()
        };
        write_diagnostic("leave:after")
    }

    scenario() -> i64 / {Diagnostic} {
        resumed();
        cancelled();
        left();
        42
    }

    struct FirstDrop { marker: i64 }
    struct SecondDrop { marker: i64 }
    struct DropPair { first: FirstDrop, second: SecondDrop }

    impl Drop for FirstDrop {
        drop(&mut self) -> { self.marker; 1 / 0; () }
    }

    impl Drop for SecondDrop {
        drop(&mut self) -> {
            self.marker;
            9223372036854775807 + 1;
            ()
        }
    }

    drop_scenario() -> () {
        let pair = DropPair {
            first: FirstDrop { marker: 1 },
            second: SecondDrop { marker: 2 }
        };
        ()
    }

    main() -> () { run_compiler_host(scenario); () }
"#;

#[derive(Clone)]
struct TraceHost(Arc<Mutex<Vec<String>>>);

impl Host for TraceHost {
    fn process_args(&self) -> Result<Vec<String>, HostFault> {
        Err(HostFault::new("unexpected process.args"))
    }

    fn fs_read(&self, _path: String) -> Result<Vec<u8>, HostFault> {
        Err(HostFault::new("unexpected fs.read"))
    }

    fn fs_write(&self, _path: String, _contents: Vec<u8>) -> Result<(), HostFault> {
        Err(HostFault::new("unexpected fs.write"))
    }

    fn diagnostic_write(&self, message: String) -> Result<(), HostFault> {
        self.0.lock().unwrap().push(message);
        Ok(())
    }
}

fn observations(level: OptimizationLevel) -> (Vec<String>, grandiose_vm::RuntimeError) {
    let phases = compile_source_to_phases_with_options(
        "optimizer-trace-equivalence.gr",
        SOURCE,
        CompileOptions {
            optimization_level: level,
        },
    )
    .unwrap_or_else(|errors| panic!("{level:?} failed to compile: {errors:#?}"));
    let entry = phases.artifact.entry_function.unwrap();
    let drop_scenario = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "drop_scenario")
        .expect("missing custom-Drop trace function") as u32;
    let trace = Arc::new(Mutex::new(Vec::new()));
    let vm = Vm::with_host(
        verify(phases.artifact).unwrap(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        TraceHost(trace.clone()),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
    let drop_fault = vm
        .run(drop_scenario, vec![])
        .expect_err("custom Drop trace must stop at the first reverse-order hook");
    drop(vm);
    (
        Arc::try_unwrap(trace).unwrap().into_inner().unwrap(),
        drop_fault,
    )
}

#[test]
fn optimization_preserves_effect_control_and_host_call_trace() {
    let baseline = observations(OptimizationLevel::O0);
    assert_eq!(
        baseline.0,
        [
            "resume:before",
            "resume:perform",
            "resume:after",
            "cancel:before",
            "cancel:perform",
            "cancel:after",
            "leave:before",
            "leave:inside",
            "leave:after",
        ]
    );
    assert_eq!(baseline.1, grandiose_vm::RuntimeError::ArithmeticOverflow);
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        assert_eq!(
            observations(level),
            baseline,
            "observable trace changed at {level:?}"
        );
    }
}
