use grandiose::compile_source_to_phases;

#[test]
fn transitive_and_mixed_row_must_perform_evidence_multiplies_ownership() {
    let source = r#"
        effect Choice { [2,2] choose() -> i64 }
        struct Ticket { marker: i64 }
        impl Use<[2,2]> for Ticket {}
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        relay() -> i64 / {Choice} { leaf() }
        selected() -> i64 {
            handle {
                let ticket = Ticket { marker: 1 };
                let answer = relay();
                let Ticket { marker } = ticket;
                answer + marker
            } {
                Choice::choose() with continuation => {
                    let ignored = resume(continuation, 19);
                    resume(move continuation, 41)
                }
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("transitive-performance.glorious", source).unwrap();
    let core = phases.core.canonical_text();
    assert!(core.contains("performance \"leaf\" normal=[2] abandon=false widened=false"));
    assert!(core.contains("performance \"relay\" normal=[2] abandon=false widened=false"));
}

#[test]
fn unused_operation_in_a_mixed_protocol_does_not_erase_body_evidence() {
    let source = r#"
        effect Choice { [2,2] choose() -> i64 [1,1] unused() -> i64 }
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("mixed-row-performance.glorious", source).unwrap();
    assert!(
        phases
            .core
            .canonical_text()
            .contains("performance \"leaf\" normal=[2] abandon=false widened=false")
    );
}

#[test]
fn grounded_generic_emission_carries_canonical_performance_evidence() {
    let source = r#"
        effect Choice { [2,2] choose() -> i64 }
        relay<T>(fallback: T) -> T / {Choice} {
            let selected = perform Choice::choose();
            fallback
        }
        selected() -> i64 {
            handle relay(41) {
                Choice::choose() with continuation => {
                    let ignored = resume(continuation, 19);
                    resume(move continuation, 41)
                }
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-performance.glorious", source).unwrap();
    assert!(phases.core.canonical_text().lines().any(|line| {
        line.contains("performance \"$specialization$relay#")
            && line.contains("normal=[2] abandon=false widened=false")
    }));
}

#[test]
fn sequential_two_shot_calls_preserve_exact_factor_four() {
    let source = r#"
        effect Choice { [2,2] choose() -> i64 }
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        twice() -> i64 / {Choice} { let first = leaf(); let second = leaf(); first + second }
        main() -> { () }
    "#;
    let first = compile_source_to_phases("factor-four.glorious", source).unwrap();
    let repeated = compile_source_to_phases("factor-four.glorious", source).unwrap();
    assert!(
        first
            .core
            .canonical_text()
            .contains("performance \"twice\" normal=[4] abandon=false widened=false")
    );
    assert_eq!(first.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), repeated.mir_fingerprint());
}

#[test]
fn arbitrary_exact_power_of_two_multiplier_accounts_live_ownership() {
    let source = r#"
        effect Choice { [2,2] choose() -> i64 }
        struct Ticket { marker: i64 }
        impl Use<[8,8]> for Ticket {}
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        eight() -> i64 / {Choice} {
            let first = leaf();
            let second = leaf();
            let third = leaf();
            first + second + third
        }
        selected() -> i64 {
            handle {
                let ticket = Ticket { marker: 1 };
                let answer = eight();
                let Ticket { marker } = ticket;
                answer + marker
            } {
                Choice::choose() with continuation => {
                    let ignored = resume(continuation, 19);
                    resume(move continuation, 41)
                }
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("factor-eight.glorious", source).unwrap();
    assert!(
        phases
            .core
            .canonical_text()
            .contains("performance \"eight\" normal=[8] abandon=false widened=false")
    );
}

#[test]
fn optional_and_terminal_sequence_order_never_manufactures_must_perform_evidence() {
    let source = r#"
        effect Choice { [2,2] choose() -> i64 }
        effect Maybe { [0,1] maybe() -> i64 }
        effect Abort { stop() -> ! }
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        optional_first() -> i64 / {Choice, Maybe} {
            let ignored = perform Maybe::maybe();
            leaf()
        }
        optional_last() -> i64 / {Choice, Maybe} {
            let selected = leaf();
            let ignored = perform Maybe::maybe();
            selected
        }
        terminal_first() -> i64 / {Choice, Abort} {
            perform Abort::stop()
        }
        terminal_last() -> i64 / {Choice, Abort} {
            let ignored = leaf();
            perform Abort::stop()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("abandonment-order.glorious", source).unwrap();
    let core = phases.core.canonical_text();
    for callable in ["optional_first", "optional_last"] {
        assert!(core.contains(&format!(
            "performance \"{callable}\" normal=[2] abandon=true widened=false"
        )));
    }
    for callable in ["terminal_first", "terminal_last"] {
        assert!(core.contains(&format!(
            "performance \"{callable}\" normal=[] abandon=true widened=false"
        )));
    }
}

#[test]
fn exhaustive_terminal_dispatch_preserves_a_direct_branch_summary() {
    let source = r#"
        effect Choice { [2,2] choose() -> i64 }
        effect Dispatch { select() -> ! }
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        conditional() -> i64 / {Choice} {
            handle perform Dispatch::select() {
                Dispatch::select() => leaf()
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("conditional-performance.glorious", source).unwrap();
    let core = phases.core.canonical_text();
    assert!(
        core.contains("performance \"conditional\" normal=[2] abandon=false widened=false"),
        "{core}"
    );
}

#[test]
fn exhaustive_terminal_enum_payload_dispatch_joins_exact_branches() {
    let source = r#"
        enum Flag { Off, On }
        effect Choice { [2,2] choose() -> i64 }
        effect Dispatch { select(flag: Flag) -> ! }
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        conditional(flag: Flag) -> i64 / {Choice} {
            handle perform Dispatch::select(flag) {
                Dispatch::select(Flag::Off) => leaf(),
                Dispatch::select(Flag::On) => leaf()
            }
        }
        main() -> { () }
    "#;
    let phases =
        compile_source_to_phases("exhaustive-payload-performance.glorious", source).unwrap();
    assert!(
        phases
            .core
            .canonical_text()
            .contains("performance \"conditional\" normal=[2] abandon=false widened=false")
    );
}

#[test]
fn nonexhaustive_terminal_payload_dispatch_cannot_authorize_caller_ownership() {
    let source = r#"
        effect Choice { [2,2] choose() -> i64 }
        effect Dispatch { select(value: i64) -> ! }
        struct Ticket { marker: i64 }
        impl Use<[2,2]> for Ticket {}
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        conditional(value: i64) -> i64 / {Choice, Dispatch} {
            handle perform Dispatch::select(value) {
                Dispatch::select(0) => leaf()
            }
        }
        selected(value: i64) -> i64 / {Dispatch} {
            handle {
                let ticket = Ticket { marker: 1 };
                let answer = conditional(value);
                let Ticket { marker } = ticket;
                answer + marker
            } {
                Choice::choose() with continuation => {
                    let ignored = resume(continuation, 19);
                    resume(move continuation, 41)
                }
            }
        }
        main() -> { () }
    "#;
    let diagnostics = compile_source_to_phases("partial-terminal-performance.glorious", source)
        .expect_err("a forwarded terminal path cannot prove an exact caller multiplier");
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("effectful call edges require path-sensitive Use analysis")
                || diagnostic
                    .message
                    .contains("cancellation/abandonment path has actual Use count 0")
        }),
        "{diagnostics:#?}"
    );
}

#[test]
fn may_effect_only_and_recursive_evidence_never_claims_a_multiplier() {
    let source = r#"
        effect Choice { [2,2] choose() -> i64 }
        may() -> i64 / {Choice} { 1 }
        recurse() -> i64 / {Choice} { recurse() }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("conservative-performance.glorious", source).unwrap();
    let core = phases.core.canonical_text();
    assert!(core.contains("performance \"may\" normal=[1] abandon=false widened=false"));
    assert!(core.contains("performance \"recurse\" normal=[] abandon=false widened=false"));
}

#[test]
fn nonreturning_effect_free_callee_cannot_lend_a_false_later_multiplier() {
    let source = r#"
        effect Choice { [2,2] choose() -> i64 }
        never() -> i64 { never() }
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        claimed() -> i64 / {Choice} {
            let unreachable = never();
            leaf() + unreachable
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("pure-nonreturn-performance.glorious", source).unwrap();
    let core = phases.core.canonical_text();
    assert!(core.contains("performance \"never\" normal=[] abandon=false widened=false"));
    assert!(core.contains("performance \"claimed\" normal=[] abandon=false widened=false"));
}

#[test]
fn acyclic_call_chain_longer_than_the_old_iteration_cap_converges() {
    let mut source = String::from(
        "effect Choice { [2,2] choose() -> i64 }\nleaf() -> i64 / {Choice} { perform Choice::choose() }\n",
    );
    for index in 0..70 {
        let callee = if index == 69 {
            "leaf".to_owned()
        } else {
            format!("relay{}", index + 1)
        };
        source.push_str(&format!(
            "relay{index}() -> i64 / {{Choice}} {{ {callee}() }}\n"
        ));
    }
    source.push_str("main() -> { () }\n");
    let phases = compile_source_to_phases("long-summary-chain.glorious", &source).unwrap();
    assert!(
        phases
            .core
            .canonical_text()
            .contains("performance \"relay0\" normal=[2] abandon=false widened=false")
    );
}

#[test]
fn transitive_summary_is_not_source_declaration_order_dependent() {
    let first = r#"
        effect Choice { [2,2] choose() -> i64 }
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        relay() -> i64 / {Choice} { leaf() }
        main() -> { () }
    "#;
    let reordered = r#"
        effect Choice { [2,2] choose() -> i64 }
        relay() -> i64 / {Choice} { leaf() }
        leaf() -> i64 / {Choice} { perform Choice::choose() }
        main() -> { () }
    "#;
    let first = compile_source_to_phases("ordered.glorious", first).unwrap();
    let reordered = compile_source_to_phases("reordered.glorious", reordered).unwrap();
    let evidence = |text: &str| {
        text.lines()
            .filter(|line| line.starts_with("performance "))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    let first_text = first.core.canonical_text();
    let reordered_text = reordered.core.canonical_text();
    assert_eq!(evidence(&first_text), evidence(&reordered_text));
}
