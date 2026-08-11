//! Release-native test support.
//!
//! Self-host integration tests must exercise the same partitioned O3/Wild
//! route used for iterative native development.  Each caller supplies a
//! temporary directory, so its durable object cache cannot be shared with a
//! concurrently running test or another worktree.

use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::source_bundle::SourceBundle;

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
}

/// Serializes the non-embedded inputs at a stable relative layout and emits a
/// release O3 executable through the CLI's private durable object cache.
///
/// The embedded standard library is intentionally omitted: `grc` supplies the
/// trusted distribution standard library itself.  Every user segment remains
/// an explicit CLI input, preserving the bundle's declaration/module graph.
pub fn build_cached_native(
    bundle: &SourceBundle,
    directory: &Path,
    executable_name: &str,
) -> PathBuf {
    let sources = directory.join("native-inputs");
    let cache = directory.join("native-incremental-cache");
    fs::create_dir_all(&sources).unwrap();
    fs::create_dir_all(&cache).unwrap();

    let user_segments = &bundle.segments()[1..];
    assert!(
        !user_segments.is_empty(),
        "native test bundle must contain a primary source segment"
    );
    let source_root = Path::new(user_segments[0].name())
        .parent()
        .expect("primary source must have a parent path");
    let mut inputs = Vec::<OsString>::with_capacity(user_segments.len());
    for segment in user_segments {
        let relative = Path::new(segment.name())
            .strip_prefix(source_root)
            .unwrap_or_else(|_| {
                panic!(
                    "native test bundle segment {} escapes primary source root {}",
                    segment.name(),
                    source_root.display()
                )
            });
        let path = sources.join(relative);
        let parent = path.parent().expect("serialized source must have parent");
        fs::create_dir_all(parent).unwrap();
        fs::write(&path, segment.source()).unwrap();
        inputs.push(path.into_os_string());
    }

    let executable = directory.join(executable_name);
    let grc = repository_root().join("target/release/grc");
    assert!(
        grc.is_file(),
        "release grc is required for native integration tests; run `tooling/ram-gate.sh cargo build --release -p grandiose --bin grc` first"
    );
    let output = Command::new(&grc)
        .current_dir(repository_root())
        .args(["-O3", "--emit", "executable", "--native-incremental-cache"])
        .arg(&cache)
        .arg("-o")
        .arg(&executable)
        .args(&inputs)
        .output()
        .expect("release grc must start for cached native integration test");
    assert!(
        output.status.success() && executable.is_file(),
        "cached native executable emission failed:\nstdout:\n{}\nstderr:\n{}\ninputs: {}\ncache: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        sources.display(),
        cache.display()
    );
    executable
}
