use grandiose::{compile_source_to_phases, compiler_mir::Terminator};

#[test]
fn perform_records_live_owner_and_reference_capture_sets_deterministically() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        observe(value: &mut i64) -> i64 { 41 }
        selected() -> i64 {
            handle {
                let value = 41;
                let reference = &mut value;
                let answer = perform Ask::ask();
                observe(reference) + answer
            } {
                Ask::ask() with continuation => resume(continuation, 1)
            }
        }
        main() -> { () }
    "#;
    let first = compile_source_to_phases("mir-capture.gr", source).unwrap();
    let repeated = compile_source_to_phases("mir-capture.gr", source).unwrap();
    assert_eq!(first.mir.canonical_text(), repeated.mir.canonical_text());
    assert_eq!(first.mir_fingerprint(), repeated.mir_fingerprint());

    let capture = first
        .mir
        .functions
        .iter()
        .flat_map(|function| &function.blocks)
        .find_map(|block| match &block.terminator {
            Terminator::Perform { capture, .. } if !capture.captured_references.is_empty() => {
                Some(capture)
            }
            _ => None,
        })
        .expect("the handled body contains a Perform terminator with a live reference");
    assert!(!capture.captured_owners.is_empty());
    assert!(!capture.captured_references.is_empty());
    assert!(
        capture
            .captured_references
            .iter()
            .all(|reference| capture.captured_owners.binary_search(reference).is_ok())
    );
}

#[test]
fn transferred_perform_payload_is_not_a_continuation_owner() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Exchange { [1,1] exchange(ticket: Ticket) -> Ticket }
        selected() -> i64 {
            let outgoing = Ticket { serial: 40 };
            handle {
                let incoming = perform Exchange::exchange(outgoing);
                let Ticket { serial } = incoming;
                serial + 2
            } {
                Exchange::exchange(ticket) with continuation => {
                    let Ticket { serial } = ticket;
                    resume(continuation, Ticket { serial: serial })
                }
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("mir-payload-capture.gr", source).unwrap();
    let (payloads, capture) = phases
        .mir
        .functions
        .iter()
        .flat_map(|function| &function.blocks)
        .find_map(|block| match &block.terminator {
            Terminator::Perform {
                payloads, capture, ..
            } => Some((payloads, capture)),
            _ => None,
        })
        .expect("selected contains a Perform terminator");
    assert!(payloads.iter().all(|payload| {
        capture
            .captured_owners
            .binary_search(&payload.register)
            .is_err()
    }));
}
