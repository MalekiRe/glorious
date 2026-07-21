use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};

/// Canonical source suffix plus the legacy compatibility suffix accepted
/// during the G1 tooling migration.
pub fn is_source_path(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|extension| extension.to_str()),
        Some("glorious" | "gr")
    )
}

/// XDG-respecting cache root for grand (`~/.cache/grandiose` by default).
pub fn cache_root() -> Result<PathBuf> {
    if let Ok(dir) = std::env::var("GRAND_CACHE_DIR") {
        return Ok(PathBuf::from(dir));
    }
    let base = match std::env::var("XDG_CACHE_HOME") {
        Ok(dir) if !dir.is_empty() => PathBuf::from(dir),
        _ => {
            let home = std::env::var("HOME").context("HOME is not set")?;
            Path::new(&home).join(".cache")
        }
    };
    Ok(base.join("grandiose"))
}

/// Walk upward from `start` looking for a directory entry named `relative`.
pub fn find_upwards(start: &Path, relative: &str) -> Option<PathBuf> {
    let mut dir = Some(start.to_path_buf());
    while let Some(current) = dir {
        let candidate = current.join(relative);
        if candidate.exists() {
            return Some(candidate);
        }
        dir = current.parent().map(Path::to_path_buf);
    }
    None
}

pub fn blake3_hex(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

/// Deterministic content hash of a package directory: every `.glorious` or
/// legacy `.gr` file plus `grandiose.toml`, in sorted relative-path order,
/// `.git` excluded.
pub fn hash_package_dir(dir: &Path) -> Result<String> {
    let mut files: Vec<PathBuf> = Vec::new();
    for entry in walkdir::WalkDir::new(dir)
        .into_iter()
        .filter_entry(|e| e.file_name() != ".git" && e.file_name() != "target")
    {
        let entry = entry?;
        if !entry.file_type().is_file() {
            continue;
        }
        let path = entry.into_path();
        let is_source = is_source_path(&path);
        let is_manifest = path.file_name().is_some_and(|n| n == "grandiose.toml");
        if is_source || is_manifest {
            files.push(path);
        }
    }
    files.sort();
    let mut hasher = blake3::Hasher::new();
    for file in files {
        let relative = file.strip_prefix(dir).unwrap_or(&file);
        hasher.update(relative.to_string_lossy().as_bytes());
        hasher.update(b"\0");
        hasher
            .update(&std::fs::read(&file).with_context(|| format!("reading {}", file.display()))?);
        hasher.update(b"\0");
    }
    Ok(format!("blake3:{}", hasher.finalize().to_hex()))
}

/// Run a command, capturing output; error (with stderr included) on failure.
pub fn run_command(mut command: Command, what: &str) -> Result<String> {
    let output = command
        .output()
        .with_context(|| format!("failed to launch {what} ({command:?})"))?;
    if !output.status.success() {
        bail!(
            "{what} failed ({}):\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim_end()
        );
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

pub fn git(args: &[&str], dir: Option<&Path>) -> Result<String> {
    let mut command = Command::new("git");
    command.args(args);
    if let Some(dir) = dir {
        command.current_dir(dir);
    }
    run_command(command, "git")
}

pub fn copy_dir(from: &Path, to: &Path) -> Result<()> {
    for entry in walkdir::WalkDir::new(from)
        .into_iter()
        .filter_entry(|e| e.file_name() != ".git" && e.file_name() != "target")
    {
        let entry = entry?;
        let relative = entry.path().strip_prefix(from)?;
        let destination = to.join(relative);
        if entry.file_type().is_dir() {
            std::fs::create_dir_all(&destination)?;
        } else if entry.file_type().is_file() {
            if let Some(parent) = destination.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::copy(entry.path(), &destination)?;
        }
    }
    Ok(())
}

pub fn valid_package_name(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some('a'..='z'))
        && chars.all(|c| matches!(c, 'a'..='z' | '0'..='9' | '-'))
}
