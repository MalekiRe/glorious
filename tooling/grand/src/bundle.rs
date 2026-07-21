use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use serde::Serialize;

use crate::resolve::{Resolution, ResolvedPackage};
use crate::util::is_source_path;

fn canonical_package_path(
    package: &ResolvedPackage,
    relative: &str,
    description: &str,
) -> Result<PathBuf> {
    let package_root = package
        .root
        .canonicalize()
        .with_context(|| format!("canonicalizing package root {}", package.root.display()))?;
    let requested = package.root.join(relative);
    let canonical = requested.canonicalize().with_context(|| {
        format!(
            "package `{}`: {description} `{relative}` does not exist",
            package.name
        )
    })?;
    if !canonical.starts_with(&package_root) {
        bail!(
            "package `{}`: {description} `{relative}` escapes the package root",
            package.name
        );
    }
    Ok(canonical)
}

/// One input file's placement inside the concatenated bundle. Written next to
/// the bundle so diagnostics pointing into it can be traced back by hand (and,
/// later, remapped automatically once the compiler reports structured spans).
#[derive(Debug, Serialize)]
pub struct Segment {
    pub package: String,
    pub file: PathBuf,
    pub start_byte: usize,
    pub byte_len: usize,
    pub start_line: usize,
    pub line_count: usize,
}

pub struct Bundle {
    pub text: String,
    pub segments: Vec<Segment>,
}

/// Source files of one package in deterministic order: every `.glorious`
/// (plus legacy `.gr`) under the configured source directories (default
/// `src/`), sorted by relative path.
/// The `entry` file, if any, is excluded here and appended separately.
pub fn package_sources(package: &ResolvedPackage) -> Result<Vec<PathBuf>> {
    let roots = package
        .manifest
        .project
        .sources
        .clone()
        .unwrap_or_else(|| vec!["src".into()]);
    let entry = package
        .manifest
        .project
        .entry
        .as_deref()
        .map(|entry| canonical_package_path(package, entry, "entry file"))
        .transpose()?;
    let mut files = Vec::new();
    for root in roots {
        let base = canonical_package_path(package, &root, "source path")?;
        if base.is_file() {
            files.push(base);
            continue;
        }
        if !base.is_dir() {
            bail!(
                "package `{}`: source path `{root}` is neither a file nor directory",
                package.name
            );
        }
        for item in walkdir::WalkDir::new(&base).sort_by_file_name() {
            let item = item?;
            if item.file_type().is_file() && is_source_path(item.path()) {
                files.push(item.into_path());
            }
        }
    }
    files.sort();
    files.dedup();
    files.retain(|f| Some(f) != entry.as_ref());
    Ok(files)
}

/// The resolution's compilation inputs in bundle order: dependencies in
/// topological order, then the root package, then the entry file last (the
/// root manifest's entry, or a substitute such as a test file). This ordered
/// list is the compilation unit — the legacy path concatenates it, the
/// multi-file path passes it to the compiler verbatim.
pub fn input_files(
    resolution: &Resolution,
    entry: Option<&Path>,
) -> Result<Vec<(String, PathBuf)>> {
    let mut files = Vec::new();
    for package in &resolution.packages {
        if package.source != "root" {
            if package.manifest.project.entry.is_some() {
                eprintln!(
                    "warning: dependency `{}` declares an entry point; it is treated as a library",
                    package.name
                );
            }
            for file in package_sources(package)? {
                files.push((package.name.clone(), file));
            }
        }
    }
    let root = resolution.root();
    for file in package_sources(root)? {
        files.push((root.name.clone(), file));
    }
    let entry = match entry {
        Some(file) => file.to_path_buf(),
        None => {
            let declared = root.manifest.project.entry.as_ref().with_context(|| {
                format!(
                    "package `{}` has no entry point; only executables can be built",
                    root.name
                )
            })?;
            canonical_package_path(root, declared, "entry file")?
        }
    };
    let canonical_root = root.root.canonicalize()?;
    let entry = entry
        .canonicalize()
        .with_context(|| format!("entry file {} does not exist", entry.display()))?;
    if !entry.starts_with(&canonical_root) {
        bail!(
            "entry file {} escapes package `{}`",
            entry.display(),
            root.name
        );
    }
    if !entry.is_file() || !is_source_path(&entry) {
        bail!(
            "entry file {} is not a Grandiose source file",
            entry.display()
        );
    }
    files.push((root.name.clone(), entry));
    if files.is_empty() {
        bail!("no source files found");
    }
    Ok(files)
}

/// Concatenate ordered inputs into a single compilation unit for compilers
/// without multi-file support.
pub fn assemble(files: &[(String, PathBuf)]) -> Result<Bundle> {
    let mut text = String::new();
    let mut segments = Vec::new();
    for (package, file) in files {
        let mut content = std::fs::read_to_string(file)
            .with_context(|| format!("reading source file {}", file.display()))?;
        if !content.ends_with('\n') {
            content.push('\n');
        }
        segments.push(Segment {
            package: package.clone(),
            file: file.clone(),
            start_byte: text.len(),
            byte_len: content.len(),
            start_line: text.lines().count() + 1,
            line_count: content.lines().count(),
        });
        text.push_str(&content);
    }
    Ok(Bundle { text, segments })
}

impl Bundle {
    /// Write bundle + segment map into `dir`, returning the bundle path.
    pub fn write(&self, dir: &Path, stem: &str) -> Result<PathBuf> {
        std::fs::create_dir_all(dir)?;
        let bundle_path = dir.join(format!("{stem}.glorious"));
        std::fs::write(&bundle_path, &self.text)
            .with_context(|| format!("writing {}", bundle_path.display()))?;
        let map_path = dir.join(format!("{stem}.map.json"));
        std::fs::write(&map_path, serde_json::to_string_pretty(&self.segments)?)?;
        Ok(bundle_path)
    }
}
