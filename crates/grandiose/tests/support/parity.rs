use std::{
    fs,
    path::{Path, PathBuf},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OracleOutcome {
    Accepted(Vec<u8>),
    Rejected { code: String },
}

pub fn glorious_corpus(directory: impl AsRef<Path>) -> Vec<PathBuf> {
    fn collect(directory: &Path, output: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(directory)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", directory.display()))
        {
            let path = entry.expect("failed to read corpus entry").path();
            if path.is_dir() {
                collect(&path, output);
            } else if path.extension().and_then(|value| value.to_str()) == Some("glorious") {
                output.push(path);
            }
        }
    }

    let mut paths = Vec::new();
    collect(directory.as_ref(), &mut paths);
    paths.sort();
    paths
}

pub fn assert_oracle_parity<T>(
    cases: impl IntoIterator<Item = T>,
    mut rust: impl FnMut(&T) -> OracleOutcome,
    mut self_host: impl FnMut(&T) -> OracleOutcome,
) where
    T: std::fmt::Debug,
{
    for case in cases {
        let expected = rust(&case);
        let actual = self_host(&case);
        assert_eq!(actual, expected, "self-host parity mismatch for {case:?}");
    }
}
