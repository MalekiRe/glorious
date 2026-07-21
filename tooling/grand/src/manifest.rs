use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use serde::Deserialize;

use crate::util::valid_package_name;

pub const MANIFEST_NAME: &str = "grandiose.toml";

/// A multi-package workspace: `[workspace] members = ["app", "libs/util"]`
/// in a grandiose.toml (with or without a `[project]` of its own). Members
/// share one lockfile at the workspace root.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkspaceDef {
    pub members: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub project: Project,
    #[serde(default)]
    pub workspace: Option<WorkspaceDef>,
    #[serde(default)]
    pub dependencies: BTreeMap<String, DependencySpec>,
    #[serde(default)]
    pub backend: Option<Backend>,
    /// Diagnostic level overrides: `"warnings" = "deny"` or per-code
    /// `GRC1234 = "allow"`. Values: allow | warn | deny.
    #[serde(default)]
    pub lints: BTreeMap<String, String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Project {
    pub name: String,
    /// Part of the manifest contract; not consumed yet (no version solving).
    #[allow(dead_code)]
    pub version: String,
    /// Executable packages have an entry file; library packages omit it.
    pub entry: Option<String>,
    /// Source globs are not supported yet; this is a list of directories (or
    /// files) relative to the package root that are scanned for `*.gr`.
    /// Defaults to `["src"]`.
    pub sources: Option<Vec<String>>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Backend {
    #[allow(dead_code)] // manifest contract; consulted when more backends exist
    pub kind: Option<String>,
    /// Checked against the installed clang major version at build time.
    #[serde(rename = "minimum-version")]
    pub minimum_version: Option<u64>,
}

/// Raw dependency table entry; validated into a [`Dependency`].
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DependencySpec {
    pub path: Option<String>,
    pub git: Option<String>,
    pub github: Option<String>,
    pub tag: Option<String>,
    pub rev: Option<String>,
    pub branch: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Dependency {
    Path { path: PathBuf },
    Git { url: String, reference: GitReference },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GitReference {
    Tag(String),
    Rev(String),
    Branch(String),
}

impl GitReference {
    pub fn describe(&self) -> String {
        match self {
            GitReference::Tag(tag) => format!("tag={tag}"),
            GitReference::Rev(rev) => format!("rev={rev}"),
            GitReference::Branch(branch) => format!("branch={branch}"),
        }
    }
}

impl Dependency {
    /// Canonical source string, as recorded in the lockfile.
    pub fn source_id(&self, base: &Path) -> String {
        match self {
            Dependency::Path { path } => {
                let absolute = base.join(path);
                let canonical = absolute.canonicalize().unwrap_or(absolute);
                format!("path+{}", canonical.display())
            }
            Dependency::Git { url, reference } => {
                format!("git+{url}?{}", reference.describe())
            }
        }
    }
}

impl DependencySpec {
    pub fn validate(&self, name: &str) -> Result<Dependency> {
        let references = [
            self.tag.clone().map(GitReference::Tag),
            self.rev.clone().map(GitReference::Rev),
            self.branch.clone().map(GitReference::Branch),
        ];
        let mut references = references.into_iter().flatten();
        let reference = references.next();
        if references.next().is_some() {
            bail!("dependency `{name}`: specify exactly one of `tag`, `rev`, `branch`");
        }
        match (&self.path, &self.git, &self.github) {
            (Some(path), None, None) => {
                if reference.is_some() {
                    bail!("dependency `{name}`: `tag`/`rev`/`branch` do not apply to path dependencies");
                }
                Ok(Dependency::Path { path: PathBuf::from(path) })
            }
            (None, Some(url), None) => Ok(Dependency::Git {
                url: url.clone(),
                reference: reference
                    .with_context(|| format!("dependency `{name}`: git dependencies need one of `tag`, `rev`, `branch`"))?,
            }),
            (None, None, Some(slug)) => Ok(Dependency::Git {
                url: format!("https://github.com/{slug}"),
                reference: reference
                    .with_context(|| format!("dependency `{name}`: github dependencies need one of `tag`, `rev`, `branch`"))?,
            }),
            _ => bail!("dependency `{name}`: specify exactly one of `path`, `git`, `github`"),
        }
    }
}

/// A parsed grandiose.toml: a package, a bare workspace root, or both.
#[derive(Debug, Clone, Deserialize)]
struct RawManifest {
    project: Option<Project>,
    #[serde(default)]
    workspace: Option<WorkspaceDef>,
    #[serde(default)]
    dependencies: BTreeMap<String, DependencySpec>,
    #[serde(default)]
    backend: Option<Backend>,
    #[serde(default)]
    lints: BTreeMap<String, String>,
}

pub enum ManifestFile {
    Package(Manifest),
    /// `[workspace]` with no `[project]`.
    WorkspaceRoot(WorkspaceDef),
}

pub fn load_any(path: &Path) -> Result<ManifestFile> {
    let text = std::fs::read_to_string(path)
        .with_context(|| format!("could not read {}", path.display()))?;
    let raw: RawManifest =
        toml::from_str(&text).with_context(|| format!("could not parse {}", path.display()))?;
    match (raw.project, raw.workspace) {
        (Some(project), workspace) => {
            let manifest = Manifest {
                project,
                workspace,
                dependencies: raw.dependencies,
                backend: raw.backend,
                lints: raw.lints,
            };
            manifest.validate_name(path)?;
            Ok(ManifestFile::Package(manifest))
        }
        (None, Some(workspace)) => Ok(ManifestFile::WorkspaceRoot(workspace)),
        (None, None) => bail!("{}: neither [project] nor [workspace] present", path.display()),
    }
}

impl Manifest {
    pub fn load(path: &Path) -> Result<Manifest> {
        match load_any(path)? {
            ManifestFile::Package(manifest) => Ok(manifest),
            ManifestFile::WorkspaceRoot(_) => bail!(
                "{} is a workspace root, not a package; select a member with -p",
                path.display()
            ),
        }
    }

    fn validate_name(&self, path: &Path) -> Result<()> {
        let manifest = self;
        if !valid_package_name(&manifest.project.name) {
            bail!(
                "{}: package name `{}` is invalid (expected [a-z][a-z0-9-]*)",
                path.display(),
                manifest.project.name
            );
        }
        Ok(())
    }

    pub fn dependencies(&self) -> Result<Vec<(String, Dependency)>> {
        self.dependencies
            .iter()
            .map(|(name, spec)| Ok((name.clone(), spec.validate(name)?)))
            .collect()
    }
}

/// Find the enclosing project: walk upward from `start` to the first
/// `grandiose.toml`. Returns (package root, manifest, lock root). The lock
/// root is the enclosing workspace root when one lists this package as a
/// member, otherwise the package root itself. `select` picks a workspace
/// member by name (or member directory name) when the search lands on a
/// workspace root — or overrides the package when inside a workspace.
pub fn find_project_in_workspace(
    start: &Path,
    select: Option<&str>,
) -> Result<(PathBuf, Manifest, PathBuf)> {
    let mut dir = Some(start.to_path_buf());
    while let Some(current) = dir {
        let manifest_path = current.join(MANIFEST_NAME);
        if manifest_path.is_file() {
            match load_any(&manifest_path)? {
                ManifestFile::Package(manifest) => {
                    let workspace_root = enclosing_workspace(&current);
                    if let (Some(select), Some(root)) = (select, &workspace_root) {
                        if manifest.project.name != select {
                            return pick_member(root, select);
                        }
                    } else if let Some(select) = select {
                        if manifest.project.name != select {
                            bail!("package `{select}` not found (current package is `{}`)", manifest.project.name);
                        }
                    }
                    let lock_root = workspace_root.unwrap_or_else(|| current.clone());
                    return Ok((current, manifest, lock_root));
                }
                ManifestFile::WorkspaceRoot(workspace) => {
                    let selected = match (select, workspace.members.as_slice()) {
                        (Some(name), _) => name.to_string(),
                        (None, [only]) => only.clone(),
                        (None, members) => bail!(
                            "{} is a workspace root; select a member with -p (members: {})",
                            current.display(),
                            members.join(", ")
                        ),
                    };
                    return pick_member(&current, &selected);
                }
            }
        }
        dir = current.parent().map(Path::to_path_buf);
    }
    bail!("no {MANIFEST_NAME} found in {} or any parent directory", start.display())
}

/// Legacy single-package lookup (used by the LSP and `add`).
pub fn find_project(start: &Path) -> Result<(PathBuf, Manifest)> {
    let (root, manifest, _) = find_project_in_workspace(start, None)?;
    Ok((root, manifest))
}

/// Nearest ancestor whose manifest declares `[workspace]` listing `package`.
fn enclosing_workspace(package: &Path) -> Option<PathBuf> {
    let mut dir = package.parent().map(Path::to_path_buf);
    while let Some(current) = dir {
        let manifest_path = current.join(MANIFEST_NAME);
        if manifest_path.is_file() {
            let members = match load_any(&manifest_path).ok()? {
                ManifestFile::WorkspaceRoot(w) => Some(w.members),
                ManifestFile::Package(m) => m.workspace.map(|w| w.members),
            };
            if let Some(members) = members {
                let is_member = members.iter().any(|m| {
                    current.join(m).canonicalize().ok()
                        == package.to_path_buf().canonicalize().ok()
                });
                if is_member {
                    return Some(current);
                }
            }
        }
        dir = current.parent().map(Path::to_path_buf);
    }
    None
}

/// Resolve `-p <name>` against a workspace root: match by package name or by
/// the member path's final component.
fn pick_member(root: &Path, select: &str) -> Result<(PathBuf, Manifest, PathBuf)> {
    let members = match load_any(&root.join(MANIFEST_NAME))? {
        ManifestFile::WorkspaceRoot(w) => w.members,
        ManifestFile::Package(m) => m.workspace.map(|w| w.members).unwrap_or_default(),
    };
    for member in &members {
        let member_dir = root.join(member);
        let manifest_path = member_dir.join(MANIFEST_NAME);
        if !manifest_path.is_file() {
            bail!("workspace member `{member}` has no {MANIFEST_NAME} ({})", member_dir.display());
        }
        let manifest = Manifest::load(&manifest_path)?;
        let path_name = Path::new(member).file_name().unwrap_or_default().to_string_lossy();
        if manifest.project.name == select || path_name == select {
            return Ok((member_dir, manifest, root.to_path_buf()));
        }
    }
    bail!("package `{select}` is not a member of the workspace at {} (members: {})", root.display(), members.join(", "))
}
