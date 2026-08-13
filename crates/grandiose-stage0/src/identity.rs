use std::{
    fmt,
    sync::atomic::{AtomicU64, Ordering},
};

/// Canonical BLAKE3 digest. It is used for content identity, never as a
/// substitute for the typed semantic identity that contains it.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Digest([u8; 32]);

impl Digest {
    /// Reconstruct a digest received through a length-checked binary boundary.
    /// Callers must still validate the product that claims this fingerprint.
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    pub fn of_bytes(bytes: &[u8]) -> Self {
        Self(*blake3::hash(bytes).as_bytes())
    }

    pub fn of_parts(parts: impl IntoIterator<Item = impl AsRef<[u8]>>) -> Self {
        let mut hasher = blake3::Hasher::new();
        for part in parts {
            let part = part.as_ref();
            hasher.update(&(part.len() as u64).to_le_bytes());
            hasher.update(part);
        }
        Self(*hasher.finalize().as_bytes())
    }

    pub fn as_bytes(self) -> [u8; 32] {
        self.0
    }
}

impl fmt::Debug for Digest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self)
    }
}

impl fmt::Display for Digest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(formatter, "{byte:02x}")?;
        }
        Ok(())
    }
}

/// Package identity is logical and stable; it is not an absolute path.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PackageKey(pub String);

/// A stable file identity is derived from its owning package and logical path,
/// rather than host checkout layout or an arena ordinal.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FileKey(pub Digest);

impl FileKey {
    pub fn new(package: &PackageKey, logical_path: &str) -> Self {
        Self(Digest::of_parts([
            package.0.as_bytes(),
            logical_path.as_bytes(),
        ]))
    }
}

/// A logical module is owned by exactly one package. Neither component is a
/// filesystem capability; the package host has already supplied every source
/// blob associated with this identity.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ModuleKey {
    pub package: PackageKey,
    pub path: String,
}

/// Stable semantic identity for a declaration. Named definitions do not use
/// source offsets, so unrelated insertions in a body cannot churn downstream
/// resolution, interface, or cache identities.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DefKey(pub Digest);

/// Database-local revision identity. Unlike a fingerprint it may not cross
/// process boundaries and is checked against its owning database.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RevisionId {
    pub database: u64,
    pub ordinal: u64,
}

static NEXT_DATABASE_ID: AtomicU64 = AtomicU64::new(1);

pub(crate) fn fresh_database_id() -> u64 {
    NEXT_DATABASE_ID.fetch_add(1, Ordering::Relaxed)
}
