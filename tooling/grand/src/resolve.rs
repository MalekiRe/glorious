use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};

use crate::lock::{LockedPackage, Lockfile};
use crate::manifest::{Dependency, GitReference, Manifest, MANIFEST_NAME};
use crate::util::{blake3_hex, cache_root, git, hash_package_dir};

#[derive(Debug, Clone)]
pub struct ResolvedPackage {
    pub name: String,
    /// Directory containing the package's manifest and sources.
    pub root: PathBuf,
    pub manifest: Manifest,
    /// Canonical source id (`path+...` / `git+...`); `root` for the root package.
    pub source: String,
    pub commit: Option<String>,
    pub content_hash: Option<String>,
    pub deps: Vec<String>,
}

/// Packages in dependency-first topological order; the root package is last.
pub struct Resolution {
    pub packages: Vec<ResolvedPackage>,
}

pub struct ResolveOptions {
    /// Refuse any lockfile change (CI mode, `GRAND_LOCKED=1`).
    pub locked: bool,
    /// Re-resolve branches/tags instead of trusting lockfile pins.
    /// `None` = trust lock; `Some([])` = update everything; `Some(names)` = those.
    pub update: Option<Vec<String>>,
    /// Refuse network access (`GRAND_OFFLINE=1`).
    pub offline: bool,
}

impl Resolution {
    pub fn root(&self) -> &ResolvedPackage {
        self.packages.last().expect("resolution always contains the root package")
    }

    /// Name-sorted so it compares stably against a loaded lockfile.
    pub fn to_lockfile(&self) -> Lockfile {
        let mut packages: Vec<LockedPackage> = self
            .packages
            .iter()
            .filter(|p| p.source != "root")
            .map(|p| LockedPackage {
                name: p.name.clone(),
                source: p.source.clone(),
                commit: p.commit.clone(),
                content_hash: p.content_hash.clone(),
                deps: p.deps.clone(),
            })
            .collect();
        packages.sort_by(|a, b| a.name.cmp(&b.name));
        Lockfile { version: 1, packages }
    }
}

struct Resolver<'a> {
    lock: Option<&'a Lockfile>,
    options: &'a ResolveOptions,
    /// name -> index into `order` (used for conflict + cycle detection).
    resolved: BTreeMap<String, String>,
    in_progress: Vec<String>,
    order: Vec<ResolvedPackage>,
    vendor_dir: PathBuf,
}

pub fn resolve(
    root_dir: &Path,
    root_manifest: &Manifest,
    lock: Option<&Lockfile>,
    options: &ResolveOptions,
) -> Result<Resolution> {
    let mut resolver = Resolver {
        lock,
        options,
        resolved: BTreeMap::new(),
        in_progress: Vec::new(),
        order: Vec::new(),
        vendor_dir: root_dir.join("vendor"),
    };
    resolver.visit(root_manifest.project.name.clone(), root_dir.to_path_buf(), "root".to_string(), None, None)?;
    Ok(Resolution { packages: resolver.order })
}

impl Resolver<'_> {
    fn visit(
        &mut self,
        name: String,
        root: PathBuf,
        source: String,
        commit: Option<String>,
        content_hash: Option<String>,
    ) -> Result<()> {
        if let Some(existing) = self.resolved.get(&name) {
            if *existing != source {
                bail!(
                    "package `{name}` is required from two different sources:\n  {existing}\n  {source}\n\
                     the flat namespace allows exactly one version of each package"
                );
            }
            return Ok(());
        }
        if self.in_progress.contains(&name) {
            bail!("dependency cycle: {} -> {name}", self.in_progress.join(" -> "));
        }
        self.in_progress.push(name.clone());

        let manifest = Manifest::load(&root.join(MANIFEST_NAME))?;
        if manifest.project.name != name && source != "root" {
            bail!(
                "dependency `{name}` resolves to a package that calls itself `{}` ({})",
                manifest.project.name,
                root.display()
            );
        }
        let mut deps = Vec::new();
        for (dep_name, dep) in manifest.dependencies()? {
            deps.push(dep_name.clone());
            let (dep_root, dep_source, dep_commit, dep_hash) = self.locate(&dep_name, &dep, &root)?;
            self.visit(dep_name, dep_root, dep_source, dep_commit, dep_hash)?;
        }

        self.in_progress.pop();
        self.resolved.insert(name.clone(), source.clone());
        self.order.push(ResolvedPackage { name, root, manifest, source, commit, content_hash, deps });
        Ok(())
    }

    /// Materialize a dependency on disk, returning (root, source id, commit, content hash).
    fn locate(
        &self,
        name: &str,
        dep: &Dependency,
        base: &Path,
    ) -> Result<(PathBuf, String, Option<String>, Option<String>)> {
        let vendored = self.vendor_dir.join(name);
        if vendored.join(MANIFEST_NAME).is_file() {
            let source = dep.source_id(base);
            // A vendored copy should match the lockfile's pinned content;
            // divergence is legal (patched vendor) but must be visible.
            if let Some(expected) = self
                .lock
                .and_then(|l| l.find(name, &source))
                .and_then(|entry| entry.content_hash.as_deref())
            {
                if hash_package_dir(&vendored)? != expected {
                    eprintln!(
                        "warning: vendored `{name}` differs from the lockfile pin \
                         (locally patched, or stale — `grand vendor` refreshes it)"
                    );
                }
            }
            eprintln!("   using vendored `{name}` ({})", vendored.display());
            return Ok((vendored, source, None, None));
        }
        match dep {
            Dependency::Path { path } => {
                let root = base.join(path);
                let root = root
                    .canonicalize()
                    .with_context(|| format!("path dependency `{name}` not found at {}", root.display()))?;
                Ok((root, dep.source_id(base), None, None))
            }
            Dependency::Git { url, reference } => {
                let source = dep.source_id(base);
                let (root, commit, hash) = self.fetch_git(name, url, reference, &source)?;
                Ok((root, source, Some(commit), Some(hash)))
            }
        }
    }

    fn fetch_git(
        &self,
        name: &str,
        url: &str,
        reference: &GitReference,
        source: &str,
    ) -> Result<(PathBuf, String, String)> {
        let cache = cache_root()?;
        let repo_id = &blake3_hex(url.as_bytes())[..16];
        let bare = cache.join("git-db").join(format!("{repo_id}.git"));
        let locked = self.lock.and_then(|l| l.find(name, source));
        let wants_update = match &self.options.update {
            None => false,
            Some(names) => names.is_empty() || names.iter().any(|n| n == name),
        };

        let commit = match locked {
            Some(entry) if !wants_update => entry
                .commit
                .clone()
                .with_context(|| format!("lock entry for `{name}` is missing a commit"))?,
            _ => {
                if self.options.locked {
                    bail!("`{name}` is not pinned in {} and GRAND_LOCKED is set", crate::lock::LOCK_NAME);
                }
                self.resolve_reference(&bare, url, reference, wants_update)
                    .with_context(|| format!("resolving git dependency `{name}` ({url}, {})", reference.describe()))?
            }
        };

        let checkout = cache.join("checkouts").join(repo_id).join(&commit);
        if !checkout.join(MANIFEST_NAME).is_file() {
            self.ensure_bare(&bare, url)?;
            if git(&["cat-file", "-e", &format!("{commit}^{{commit}}")], Some(&bare)).is_err() {
                self.fetch_bare(&bare, url)?;
            }
            let staging = checkout.with_extension("part");
            let _ = std::fs::remove_dir_all(&staging);
            std::fs::create_dir_all(staging.parent().unwrap())?;
            git(
                &["clone", "--shared", "--no-checkout", bare.to_str().unwrap(), staging.to_str().unwrap()],
                None,
            )?;
            git(&["checkout", "--detach", &commit], Some(&staging))?;
            std::fs::rename(&staging, &checkout).context("moving checkout into place")?;
            if !checkout.join(MANIFEST_NAME).is_file() {
                bail!("git dependency `{name}` ({url}@{commit}) has no {MANIFEST_NAME} at its root");
            }
        }

        let hash = hash_package_dir(&checkout)?;
        if let Some(expected) = locked.and_then(|l| l.content_hash.as_deref()) {
            if expected != hash && !wants_update {
                bail!(
                    "content hash mismatch for `{name}` ({commit}):\n  locked:  {expected}\n  on disk: {hash}\n\
                     the cache checkout was modified; run `grand clean --cache` or `grand update {name}`"
                );
            }
        }
        Ok((checkout, commit, hash))
    }

    fn ensure_bare(&self, bare: &Path, url: &str) -> Result<()> {
        if bare.is_dir() {
            return Ok(());
        }
        if self.options.offline {
            bail!("`{url}` is not cached and GRAND_OFFLINE is set");
        }
        std::fs::create_dir_all(bare.parent().unwrap())?;
        git(&["clone", "--bare", url, bare.to_str().unwrap()], None)?;
        Ok(())
    }

    fn fetch_bare(&self, bare: &Path, url: &str) -> Result<()> {
        if self.options.offline {
            bail!("`{url}` needs a fetch and GRAND_OFFLINE is set");
        }
        git(
            &["fetch", "--force", url, "+refs/heads/*:refs/heads/*", "+refs/tags/*:refs/tags/*"],
            Some(bare),
        )?;
        Ok(())
    }

    fn resolve_reference(
        &self,
        bare: &Path,
        url: &str,
        reference: &GitReference,
        refresh: bool,
    ) -> Result<String> {
        self.ensure_bare(bare, url)?;
        // Tags and branches move upstream; a cached ref that still rev-parses
        // may be stale, so an explicit update must fetch before resolving.
        let movable = matches!(reference, GitReference::Tag(_) | GitReference::Branch(_));
        if refresh && movable && !self.options.offline {
            self.fetch_bare(bare, url)?;
        }
        let spec = match reference {
            GitReference::Tag(tag) => format!("refs/tags/{tag}^{{commit}}"),
            GitReference::Branch(branch) => format!("refs/heads/{branch}^{{commit}}"),
            GitReference::Rev(rev) => format!("{rev}^{{commit}}"),
        };
        match git(&["rev-parse", "--verify", &spec], Some(bare)) {
            Ok(commit) => Ok(commit),
            // Branches and tags move / appear after the initial clone: refetch once.
            Err(_) => {
                self.fetch_bare(bare, url)?;
                git(&["rev-parse", "--verify", &spec], Some(bare))
            }
        }
    }
}
