//! Atomic publication of host-owned compiler outputs.
//!
//! Semantic compilation never receives a host path, but command adapters do.
//! This is their final publication boundary: bytes are fully written and
//! flushed to a private sibling before one rename makes them visible at the
//! requested path.  A failed write therefore cannot truncate an older
//! artifact or leave a partial new artifact under its final name.

use std::{
    fs::{self, File, OpenOptions},
    io::{self, Write},
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_TEMPORARY: AtomicU64 = AtomicU64::new(0);

/// Failure while atomically publishing one host-owned output file.
#[derive(Debug)]
pub enum AtomicWriteError {
    InvalidTarget { path: PathBuf },
    Io { path: PathBuf, source: io::Error },
}

impl std::fmt::Display for AtomicWriteError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidTarget { path } => {
                write!(formatter, "output path `{}` has no file name", path.display())
            }
            Self::Io { path, source } => write!(formatter, "{}: {source}", path.display()),
        }
    }
}

impl std::error::Error for AtomicWriteError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidTarget { .. } => None,
            Self::Io { source, .. } => Some(source),
        }
    }
}

/// Replace `path` with `bytes` through a same-directory temporary file.
///
/// The parent directory must already exist; creating output directories is an
/// orchestration decision, not an implicit compiler capability.  The helper
/// never falls back to a cross-directory temporary because such a move can
/// degrade from an atomic rename into a copy-and-delete operation.
pub fn write_atomically(path: impl AsRef<Path>, bytes: &[u8]) -> Result<(), AtomicWriteError> {
    let path = path.as_ref();
    let parent = path.parent().filter(|parent| !parent.as_os_str().is_empty());
    let parent = parent.unwrap_or_else(|| Path::new("."));
    let name = path
        .file_name()
        .ok_or_else(|| AtomicWriteError::InvalidTarget {
            path: path.to_owned(),
        })?;
    let temporary = create_temporary(parent, name)?;

    let result = (|| -> io::Result<()> {
        let mut file = temporary.file;
        file.write_all(bytes)?;
        // The contents cross their durable file boundary before the rename
        // makes the final name visible. Directory syncing is intentionally
        // best-effort because it is not available on every supported host.
        file.sync_all()?;
        drop(file);
        fs::rename(&temporary.path, path)?;
        Ok(())
    })();
    if let Err(source) = result {
        // Before a successful rename the final path was untouched. Removal is
        // best effort because the original I/O error is the useful diagnosis.
        let _ = fs::remove_file(&temporary.path);
        return Err(AtomicWriteError::Io {
            path: path.to_owned(),
            source,
        });
    }
    Ok(())
}

struct TemporaryOutput {
    path: PathBuf,
    file: File,
}

fn create_temporary(parent: &Path, name: &std::ffi::OsStr) -> Result<TemporaryOutput, AtomicWriteError> {
    for _ in 0..128 {
        let ordinal = NEXT_TEMPORARY.fetch_add(1, Ordering::Relaxed);
        let candidate = parent.join(format!(
            ".{}.stage0-{}-{ordinal}.tmp",
            name.to_string_lossy(),
            std::process::id()
        ));
        match OpenOptions::new().write(true).create_new(true).open(&candidate) {
            Ok(file) => return Ok(TemporaryOutput {
                path: candidate,
                file,
            }),
            Err(source) if source.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(source) => {
                return Err(AtomicWriteError::Io {
                    path: candidate,
                    source,
                });
            }
        }
    }
    Err(AtomicWriteError::Io {
        path: parent.join(name),
        source: io::Error::new(
            io::ErrorKind::AlreadyExists,
            "could not reserve an atomic output temporary name",
        ),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    fn temporary_directory() -> PathBuf {
        let ordinal = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "grandiose-stage0-atomic-output-{}-{ordinal}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        directory
    }

    fn temporary_files(directory: &Path) -> Vec<PathBuf> {
        fs::read_dir(directory)
            .unwrap()
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "tmp"))
            .collect()
    }

    #[test]
    fn atomic_write_replaces_an_existing_output_without_leaving_staging_files() {
        let directory = temporary_directory();
        let output = directory.join("program.grbc");
        fs::write(&output, b"old artifact").unwrap();

        write_atomically(&output, b"new verified artifact").unwrap();

        assert_eq!(fs::read(&output).unwrap(), b"new verified artifact");
        assert!(temporary_files(&directory).is_empty());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn atomic_write_failure_preserves_the_existing_target_and_removes_staging() {
        let directory = temporary_directory();
        let target_directory = directory.join("artifact.grbc");
        fs::create_dir(&target_directory).unwrap();
        fs::write(target_directory.join("sentinel"), b"old visible state").unwrap();

        assert!(write_atomically(&target_directory, b"new artifact").is_err());

        assert_eq!(
            fs::read(target_directory.join("sentinel")).unwrap(),
            b"old visible state"
        );
        assert!(temporary_files(&directory).is_empty());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn atomic_write_does_not_create_missing_output_parents() {
        let directory = temporary_directory();
        let missing_parent = directory.join("not-created");
        let output = missing_parent.join("artifact.grbc");

        assert!(write_atomically(&output, b"artifact").is_err());

        assert!(!missing_parent.exists());
        fs::remove_dir_all(directory).unwrap();
    }
}
