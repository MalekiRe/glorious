mod support;

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use support::parity::{OracleOutcome, assert_oracle_parity, glorious_corpus};

const MANIFEST: &str = include_str!("self_host_parity.tsv");
const FAMILIES: &[&str] = &[
    "backend_runtime",
    "compiler_pipeline",
    "effects_control",
    "mir_lowering",
    "modules_cli_sessions",
    "optimization_specialization",
    "ownership_lifetimes",
    "parity_infrastructure",
    "self_host_pipeline",
    "standard_library",
    "syntax_frontend",
    "types_traits_generics",
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Status {
    Unported,
    Partial,
    Covered,
}

#[derive(Debug)]
struct Link<'a> {
    file: &'a str,
    test: &'a str,
}

#[derive(Debug)]
struct Entry<'a> {
    family: &'a str,
    status: Status,
    links: Vec<Link<'a>>,
}

fn tests_directory() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests")
}

fn parse_manifest() -> BTreeMap<&'static str, Entry<'static>> {
    let mut entries = BTreeMap::new();
    for (index, line) in MANIFEST.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let columns = line.split('\t').collect::<Vec<_>>();
        assert_eq!(
            columns.len(),
            4,
            "manifest line {} must have four tab-separated columns",
            index + 1
        );
        let status = match columns[2] {
            "unported" => Status::Unported,
            "partial" => Status::Partial,
            "covered" => Status::Covered,
            other => panic!("manifest line {} has unknown status {other:?}", index + 1),
        };
        let links = if columns[3] == "-" {
            Vec::new()
        } else {
            columns[3]
                .split(',')
                .map(|link| {
                    let (file, test) = link.split_once('#').unwrap_or_else(|| {
                        panic!("manifest line {} has malformed link {link:?}", index + 1)
                    });
                    Link { file, test }
                })
                .collect()
        };
        assert!(
            entries
                .insert(
                    columns[0],
                    Entry {
                        family: columns[1],
                        status,
                        links
                    }
                )
                .is_none(),
            "manifest repeats {}",
            columns[0]
        );
    }
    entries
}

fn integration_suites() -> BTreeSet<String> {
    fs::read_dir(tests_directory())
        .expect("failed to read integration-test directory")
        .map(|entry| entry.expect("failed to read integration-test entry").path())
        .filter(|path| path.extension().and_then(|value| value.to_str()) == Some("rs"))
        .map(|path| path.file_name().unwrap().to_string_lossy().into_owned())
        .collect()
}

fn declares_test(source: &str, test: &str) -> bool {
    let needle = format!("fn {test}(");
    let Some(offset) = source.find(&needle) else {
        return false;
    };
    source[..offset]
        .lines()
        .rev()
        .take_while(|line| {
            let trimmed = line.trim();
            trimmed.is_empty()
                || trimmed.starts_with("#[")
                || trimmed.starts_with("//")
        })
        .any(|line| line.trim() == "#[test]")
}

fn validate_entry(file: &str, entry: &Entry<'_>, tests: &Path) -> Result<(), String> {
    let families = FAMILIES.iter().copied().collect::<BTreeSet<_>>();
    if !families.contains(entry.family) {
        return Err(format!(
            "{file} has unknown semantic family {:?}",
            entry.family
        ));
    }
    match entry.status {
        Status::Unported if !entry.links.is_empty() => {
            return Err(format!("{file} is unported but claims parity links"));
        }
        Status::Covered if entry.links.is_empty() => {
            return Err(format!(
                "{file} is covered without an executable parity test"
            ));
        }
        Status::Unported | Status::Partial | Status::Covered => {}
    }
    for link in &entry.links {
        if !link.file.starts_with("self_host_") || !link.file.ends_with(".rs") {
            return Err(format!("{file} links non-self-host suite {}", link.file));
        }
        let source = fs::read_to_string(tests.join(link.file))
            .map_err(|error| format!("{file} links missing {}: {error}", link.file))?;
        if !declares_test(&source, link.test) {
            return Err(format!(
                "{file} links missing #[test] {}#{}",
                link.file, link.test
            ));
        }
    }
    Ok(())
}

#[test]
fn parity_manifest_is_complete_and_truthful() {
    let entries = parse_manifest();
    let actual = integration_suites();
    let declared = entries
        .keys()
        .map(|value| (*value).to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        declared, actual,
        "self_host_parity.tsv must inventory every integration-test suite exactly once"
    );

    for (file, entry) in entries {
        validate_entry(file, &entry, &tests_directory()).unwrap_or_else(|error| panic!("{error}"));
    }
}

#[test]
fn covered_entries_require_a_real_self_host_test() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("self_host_example.rs"),
        "fn helper() {}\n#[test]\nfn actual_parity_test() {}\n",
    )
    .unwrap();

    let missing_link = Entry {
        family: "self_host_pipeline",
        status: Status::Covered,
        links: Vec::new(),
    };
    assert!(validate_entry("example.rs", &missing_link, directory.path()).is_err());

    let helper_link = Entry {
        family: "self_host_pipeline",
        status: Status::Covered,
        links: vec![Link {
            file: "self_host_example.rs",
            test: "helper",
        }],
    };
    assert!(validate_entry("example.rs", &helper_link, directory.path()).is_err());

    let test_link = Entry {
        family: "self_host_pipeline",
        status: Status::Covered,
        links: vec![Link {
            file: "self_host_example.rs",
            test: "actual_parity_test",
        }],
    };
    validate_entry("example.rs", &test_link, directory.path()).unwrap();
}

#[test]
fn unported_entries_are_inventory_not_false_failures() {
    let entry = Entry {
        family: "compiler_pipeline",
        status: Status::Unported,
        links: Vec::new(),
    };
    validate_entry("future_suite.rs", &entry, Path::new("unused")).unwrap();
}

#[test]
fn corpus_collection_is_recursive_and_deterministic() {
    let directory = tempfile::tempdir().unwrap();
    fs::create_dir(directory.path().join("nested")).unwrap();
    fs::write(directory.path().join("z.glorious"), "z").unwrap();
    fs::write(directory.path().join("nested/a.glorious"), "a").unwrap();
    fs::write(directory.path().join("ignored.txt"), "ignored").unwrap();
    let relative = glorious_corpus(directory.path())
        .into_iter()
        .map(|path| path.strip_prefix(directory.path()).unwrap().to_owned())
        .collect::<Vec<_>>();
    assert_eq!(
        relative,
        [
            PathBuf::from("nested/a.glorious"),
            PathBuf::from("z.glorious")
        ]
    );
}

#[test]
fn oracle_helper_checks_positive_and_rejection_outcomes() {
    let cases = ["ok", "bad"];
    let oracle = |case: &&str| match *case {
        "ok" => OracleOutcome::Accepted(vec![1, 2, 3]),
        _ => OracleOutcome::Rejected {
            code: "G1000".to_owned(),
        },
    };
    assert_oracle_parity(cases, oracle, oracle);
}
