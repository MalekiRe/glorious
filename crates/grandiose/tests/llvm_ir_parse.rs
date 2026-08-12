use std::{fs, process::Command};

#[test]
fn emitted_ir_uses_explicitly_named_temporaries_and_parses() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-named-temporaries.glorious",
        r#"
            struct Owner { prefix: i64, value: i64 }
            unit_option() -> Option<()> { Option::Some(()) }
            write(value: &mut i64) { *value = 42; () }
            selected() -> i64 {
                let owner = Owner { prefix: 7, value: 11 };
                let projected = &mut owner.value;
                let crossed = handle unit_option() {
                    Result::Ok(_) => (),
                    Result::Err(_) => ()
                };
                crossed;
                write(projected);
                owner.value
            }
            main() -> () { selected(); () }
        "#,
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O2,
        },
    )
    .unwrap();
    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();

    // Numeric LLVM names use the parser's implicit numbering namespace, which
    // also includes unnamed parameters and blocks.  The backend must instead
    // give every generated SSA value an explicit name.
    assert!(module.ir.contains("%g1.tmp.0"), "{}", module.ir);
    assert!(
        !module.ir.lines().any(|line| line.trim_start().starts_with("%0 =")),
        "{}",
        module.ir
    );

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("module.ll");
    let object = directory.path().join("module.o");
    fs::write(&source, module.ir).unwrap();
    let output = Command::new("clang")
        .args(["-x", "ir", "-c"])
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
