use grandiose::compile_source_to_phases;

const SOURCE: &str = r#"
manual_result(value: Result<usize, usize>) -> Result<usize, usize> {
    @done: Result<usize, usize> {
        let found = handle value {
            Result::Ok(inner) => inner,
            Result::Err(error) => @done(Result::Err(error))
        };
        Result::Ok(found)
    }
}

manual_option(value: Option<usize>, missing: usize) -> usize {
    @missing: usize {
        handle value {
            Option::Some(inner) => inner,
            None => @missing(missing)
        }
    }
}

manual_walk(index: usize, end: usize, output: &mut Vec<usize>) {
    if(index == end) {
        ()
    } else {
        Vec::push(output, index);
        manual_walk(index + 1, end, output)
    }
}

manual_fold_impl(index: usize, end: usize, total: usize) -> usize {
    if(index == end) {
        total
    } else {
        manual_fold_impl(index + 1, end, total + index)
    }
}

manual_find_impl(index: usize, end: usize, target: usize) -> Option<usize> {
    if(index == end) {
        None
    } else {
        if(index == target) {
            Option::Some(index)
        } else {
            manual_find_impl(index + 1, end, target)
        }
    }
}

manual_builder(output: &mut Vec<usize>) -> Range<usize> {
    let start = Vec::len(&*output);
    Vec::push(output, 1);
    Vec::push(output, 2);
    let end = Vec::len(&*output);
    Range { start: start, end: end }
}

manual_restore(output: &mut Vec<usize>) -> usize {
    let mark = Vec::len(&*output);
    Vec::push(output, 4);
    let answer = Vec::len(&*output);
    Vec::truncate(output, mark);
    answer
}

main() -> () { () }
"#;

fn apply_fix(source: &str, code: &str) -> String {
    let phases = compile_source_to_phases("control-lints.glorious", source)
        .unwrap_or_else(|errors| panic!("{errors:#?}"));
    let diagnostic = phases
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code.as_deref() == Some(code))
        .unwrap_or_else(|| panic!("missing `{code}` diagnostic: {:#?}", phases.diagnostics));
    let fix = diagnostic
        .fix
        .as_ref()
        .unwrap_or_else(|| panic!("`{code}` did not provide a machine-applicable fix"));
    let mut fixed = source.to_owned();
    fixed.replace_range(fix.span.start..fix.span.end, &fix.replacement);
    fixed
}

#[test]
fn exact_manual_propagation_idioms_have_compiling_machine_fixes() {
    let result_fixed = apply_fix(SOURCE, "manual_result_propagation");
    compile_source_to_phases("result-fixed.glorious", &result_fixed)
        .unwrap_or_else(|errors| panic!("result fix did not compile: {errors:#?}\n{result_fixed}"));

    let option_fixed = apply_fix(SOURCE, "manual_option_match");
    compile_source_to_phases("option-fixed.glorious", &option_fixed)
        .unwrap_or_else(|errors| panic!("option fix did not compile: {errors:#?}\n{option_fixed}"));
}

#[test]
fn propagation_lints_are_silent_after_both_fixes_are_applied() {
    let result_fixed = apply_fix(SOURCE, "manual_result_propagation");
    let fixed = apply_fix(&result_fixed, "manual_option_match");
    let phases = compile_source_to_phases("fully-fixed.glorious", &fixed)
        .unwrap_or_else(|errors| panic!("{errors:#?}\n{fixed}"));
    assert!(
        phases.diagnostics.iter().all(|diagnostic| !matches!(
            diagnostic.code.as_deref(),
            Some("manual_result_propagation" | "manual_option_match")
        )),
        "fixed source retained propagation lints: {:#?}",
        phases.diagnostics
    );
}

#[test]
fn exact_recursive_engines_have_compiling_machine_fixes() {
    for code in ["manual_range_walk", "manual_fold", "manual_find"] {
        let fixed = apply_fix(SOURCE, code);
        compile_source_to_phases("recursive-fixed.glorious", &fixed)
            .unwrap_or_else(|errors| panic!("`{code}` fix did not compile: {errors:#?}\n{fixed}"));
    }
}

#[test]
fn exact_manual_builder_range_has_a_compiling_machine_fix() {
    let fixed = apply_fix(SOURCE, "manual_builder_range");
    compile_source_to_phases("builder-fixed.glorious", &fixed)
        .unwrap_or_else(|errors| panic!("builder fix did not compile: {errors:#?}\n{fixed}"));
}

#[test]
fn exact_manual_scope_restore_has_a_compiling_machine_fix() {
    let fixed = apply_fix(SOURCE, "manual_scope_restore");
    compile_source_to_phases("restore-fixed.glorious", &fixed)
        .unwrap_or_else(|errors| panic!("scope fix did not compile: {errors:#?}\n{fixed}"));
}
