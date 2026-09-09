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
        fmt::Display::fmt(self, formatter)
    }
}

impl fmt::Display for Digest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Digests recur in every source span and many frozen fingerprints.
        // Produce the same lowercase bytes without 32 formatting dispatches.
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut encoded = [0; 64];
        for (byte, pair) in self.0.iter().zip(encoded.chunks_exact_mut(2)) {
            pair[0] = HEX[(byte >> 4) as usize];
            pair[1] = HEX[(byte & 15) as usize];
        }
        formatter.write_str(std::str::from_utf8(&encoded).expect("hex alphabet is ASCII"))
    }
}

/// Package identity is logical and stable; it is not an absolute path.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PackageKey(pub String);

/// The source-level module binding for one manifest package identity.
///
/// Package identity deliberately preserves the exact manifest spelling and
/// version, while paths in Glorious use ordinary identifiers.  Generation one
/// therefore maps the manifest's conventional hyphen spelling to `_` before
/// resolution.  Invalid aliases are rejected when a request is normalized;
/// this helper returns `None` so defensive consumers of independently
/// constructed interface products fail closed rather than inventing a raw
/// textual fallback.
pub fn package_module_alias(package: &PackageKey) -> Option<String> {
    let name = package
        .0
        .split_once('@')
        .map_or(package.0.as_str(), |(name, _)| name);
    let alias = name.replace('-', "_");
    let mut bytes = alias.bytes();
    match bytes.next() {
        Some(byte) if byte.is_ascii_alphabetic() || byte == b'_' => {}
        _ => return None,
    }
    bytes
        .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        .then_some(alias)
}

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

/// Stable identity for one named method owned by an implementation. The
/// implementation key is itself contract-derived, so executable method-body
/// edits cannot churn selection evidence or the eventual lowered callable.
pub fn implementation_method_key(implementation: DefKey, name: &str) -> DefKey {
    DefKey(Digest::of_parts([
        b"grandiose-stage0-implementation-method-v1".as_slice(),
        implementation.0.as_bytes().as_slice(),
        name.as_bytes(),
    ]))
}

/// Database-local revision identity. Unlike a fingerprint it may not cross
/// process boundaries and is checked against its owning database.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RevisionId {
    pub database: u64,
    pub ordinal: u64,
}

static NEXT_DATABASE_ID: AtomicU64 = AtomicU64::new(1);

#[doc(hidden)]
pub fn fresh_database_id() -> u64 {
    NEXT_DATABASE_ID.fetch_add(1, Ordering::Relaxed)
}

/// Lexical module authority is package-specific and delimiter-aware.
/// Shared by declaration visibility and resolved names; textual prefix
/// collisions must not widen private access.
pub fn requester_has_lexical_authority(requester: &ModuleKey, defining_module: &ModuleKey) -> bool {
    requester.package == defining_module.package
        && (requester.path == defining_module.path
            || requester.path.strip_prefix(&defining_module.path)
                .is_some_and(|suffix| suffix.starts_with("::")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn buffered_digest_formatting_preserves_every_byte_and_nested_identity() {
        for offset in 0_u8..=u8::MAX {
            let bytes = std::array::from_fn(|index| offset.wrapping_add(index as u8));
            let digest = Digest(bytes);
            let old = bytes.iter().map(|byte| format!("{byte:02x}")).collect::<String>();
            assert_eq!(format!("{digest}"), old);
            assert_eq!(format!("{digest:?}"), old);
            assert_eq!(format!("{digest:#?}"), old);
            assert_eq!(format!("{digest:>80}"), old);
            assert_eq!(format!("{digest:.10}"), old);
            assert_eq!(format!("{:?}", FileKey(digest)), format!("FileKey({old})"));
            assert_eq!(format!("{:?}", DefKey(digest)), format!("DefKey({old})"));
        }
    }
}
