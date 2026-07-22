use std::collections::{BTreeMap, BTreeSet};

use grandiose::semantic::semantic_snapshot;
use grandiose::source_bundle::{Segment, SourceBundle};
use grandiose::{CompileOptions, OptimizationLevel, compile_bundle_to_phases_with_options};

#[test]
fn typed_core_exports_exact_shadowed_and_destructured_local_identities() {
    let primary = r#"
struct Pair { left: i64, right: i64 }
selected(seed: i64) -> i64 {
    let chosen = seed;
    {
        let pair = Pair { left: seed, right: 2 };
        let Pair { left: chosen, right: _ } = pair;
        chosen
    }
}
main() -> () { () }

"#;
    let secondary = "helper(value: i64) -> i64 { value }\n";
    let bundle = SourceBundle::distributed(
        Segment::new("主.glorious", primary),
        [Segment::new("helper.glorious", secondary)],
    );
    let phases = compile_bundle_to_phases_with_options(
        &bundle,
        CompileOptions {
            optimization_level: OptimizationLevel::O0,
        },
    )
    .unwrap();
    let snapshot = semantic_snapshot(&bundle, &phases);
    let selected_body = snapshot
        .bodies
        .iter()
        .find(|body| body.identity == "body:selected")
        .expect("principal source body snapshot");
    assert_eq!(selected_body.file, "主.glorious");
    assert!(selected_body.source_fingerprint != 0);
    assert!(
        selected_body
            .locals
            .iter()
            .any(|local| local.name == "chosen")
    );

    let chosen = snapshot
        .locals
        .iter()
        .filter(|local| local.name == "chosen")
        .max_by_key(|local| local.definition_start_byte)
        .expect("destructured binding");
    assert_eq!(
        snapshot
            .locals
            .iter()
            .filter(|local| local.name == "chosen")
            .count(),
        2,
        "shadowed bindings need distinct semantic identities"
    );
    assert_eq!(chosen.file, "主.glorious");
    assert_eq!(chosen.inferred_type, "i64");
    assert_eq!(
        &primary[chosen.definition_start_byte..chosen.definition_end_byte],
        "chosen"
    );
    let chosen_occurrences = snapshot
        .occurrences
        .iter()
        .filter(|occurrence| occurrence.identity == chosen.identity)
        .collect::<Vec<_>>();
    assert_eq!(chosen_occurrences.len(), 2, "{chosen_occurrences:#?}");
    assert!(
        chosen_occurrences
            .iter()
            .any(|occurrence| occurrence.definition)
    );

    let parameter = snapshot
        .locals
        .iter()
        .find(|local| local.file == "helper.glorious" && local.name == "value")
        .expect("secondary-file parameter");
    assert_eq!(parameter.inferred_type, "i64");
    assert_eq!(
        snapshot
            .occurrences
            .iter()
            .filter(|occurrence| occurrence.identity == parameter.identity)
            .count(),
        2
    );
}

#[test]
fn generated_handler_functions_do_not_publish_conflicting_source_spans() {
    let source = r#"
effect Stop { stop() -> ! }
selected() -> i64 {
    let captured = 42;
    handle perform Stop::stop() {
        Stop::stop() => captured
    }
}
main() -> () { () }
"#;
    let bundle = SourceBundle::distributed(Segment::new("handler.glorious", source), []);
    let phases = compile_bundle_to_phases_with_options(
        &bundle,
        CompileOptions {
            optimization_level: OptimizationLevel::O0,
        },
    )
    .unwrap();
    let snapshot = semantic_snapshot(&bundle, &phases);
    let mut occurrence_identities = BTreeMap::<_, BTreeSet<_>>::new();
    for occurrence in &snapshot.occurrences {
        occurrence_identities
            .entry((
                occurrence.file.as_str(),
                occurrence.start_byte,
                occurrence.end_byte,
            ))
            .or_default()
            .insert(occurrence.identity.as_str());
    }
    assert!(
        occurrence_identities
            .values()
            .all(|identities| identities.len() == 1),
        "one source token acquired multiple generated identities: {occurrence_identities:#?}"
    );
    let captured = snapshot
        .locals
        .iter()
        .find(|local| local.name == "captured")
        .expect("captured local definition");
    assert_eq!(
        snapshot
            .occurrences
            .iter()
            .filter(|occurrence| occurrence.identity == captured.identity)
            .count(),
        2,
        "capture lowering must not invent a second source identity"
    );
    let expression_keys = snapshot
        .expressions
        .iter()
        .map(|expression| {
            (
                expression.file.as_str(),
                expression.start_byte,
                expression.end_byte,
            )
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(expression_keys.len(), snapshot.expressions.len());
}
