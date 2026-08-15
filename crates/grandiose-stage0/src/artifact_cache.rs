//! Content-addressed persistent cache for verified VM programs.
//!
//! This cache is deliberately a host-supplied adapter rather than state owned
//! by semantic queries.  Its sole key is the complete normalized input world,
//! which already commits to compiler generations, source bytes, dependencies,
//! target, options, capabilities, runtime manifest, and bootstrap stage.
//! Entries are untrusted: a hit is accepted only after its envelope, checksum,
//! canonical VM decoding, and independent verifier proof all succeed.

use std::{
    fs::{self, File},
    io::{self, Read},
    path::{Path, PathBuf},
    sync::Mutex,
};

use crate::{
    Digest, NormalizedInputWorld, VerifiedVmProgram, decode_and_verify_program, write_atomically,
};

const CACHE_MAGIC: [u8; 8] = *b"G0AC\r\n\x1a\n";
/// Schema for the cache envelope, independent from the VM program schema.
pub const STAGE0_ARTIFACT_CACHE_SCHEMA: u32 = 1;
/// A cache file larger than this is rejected before it is read into memory.
/// Hosts with a larger trusted storage policy can opt in explicitly.
pub const DEFAULT_MAX_ARTIFACT_CACHE_ENTRY_BYTES: u64 = 512 * 1024 * 1024;
const ENVELOPE_BYTES: usize = 8 + 4 + 32 + 32 + 32 + 8;

/// Inspection-only cache accounting. Rejected entries include malformed,
/// stale, oversized, unreadable, and verifier-rejected cache records.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ArtifactCacheStats {
    pub hits: u64,
    pub misses: u64,
    pub rejected: u64,
    pub stores: u64,
}

/// Failure while creating or publishing a persistent cache entry. A store
/// failure is deliberately separate from source compilation: callers may
/// report it as tooling telemetry and still retain the verified fresh result.
#[derive(Debug)]
pub enum ArtifactCacheStoreError {
    Io { path: PathBuf, source: io::Error },
    EntryTooLarge { found: u64, limit: u64 },
}

impl std::fmt::Display for ArtifactCacheStoreError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io { path, source } => write!(formatter, "{}: {source}", path.display()),
            Self::EntryTooLarge { found, limit } => write!(
                formatter,
                "verified program cache entry is {found} bytes, exceeding its {limit}-byte limit"
            ),
        }
    }
}

impl std::error::Error for ArtifactCacheStoreError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            Self::EntryTooLarge { .. } => None,
        }
    }
}

/// A persistent, content-addressed store of verified executable programs.
#[derive(Debug)]
pub struct PersistentArtifactCache {
    root: PathBuf,
    max_entry_bytes: u64,
    stats: Mutex<ArtifactCacheStats>,
}

impl PersistentArtifactCache {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self::with_max_entry_bytes(root, DEFAULT_MAX_ARTIFACT_CACHE_ENTRY_BYTES)
    }

    pub fn with_max_entry_bytes(root: impl Into<PathBuf>, max_entry_bytes: u64) -> Self {
        Self {
            root: root.into(),
            // A zero bound cannot safely represent even an empty VM program.
            max_entry_bytes: max_entry_bytes.max(ENVELOPE_BYTES as u64),
            stats: Mutex::new(ArtifactCacheStats::default()),
        }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn stats(&self) -> ArtifactCacheStats {
        *self.stats.lock().expect("artifact cache stats mutex poisoned")
    }

    /// Load an executable only when it is exactly keyed to `world` and still
    /// crosses the decoder/verifier boundary successfully. All malformed or
    /// unavailable cache data is an optimization miss, never a compiler error.
    pub fn load(&self, world: &NormalizedInputWorld) -> Option<VerifiedVmProgram> {
        let path = self.entry_path(world.fingerprint);
        // Inspect the directory entry itself rather than following a cache
        // symlink. A cache record is untrusted input, not authority to read a
        // file elsewhere in the host filesystem.
        let metadata = match fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                self.record(|stats| stats.misses += 1);
                return None;
            }
            Err(_) => {
                self.record(|stats| stats.rejected += 1);
                return None;
            }
        };
        if !metadata.is_file()
            || metadata.file_type().is_symlink()
            || metadata.len() > self.max_entry_bytes
        {
            self.record(|stats| stats.rejected += 1);
            return None;
        }
        let Ok(file) = File::open(&path) else {
            self.record(|stats| stats.rejected += 1);
            return None;
        };
        // Do not trust a size observed before opening the file: a hostile
        // cache writer can replace or extend it between metadata and read.
        // `take` caps allocation and I/O even in that race, while one extra
        // byte distinguishes an exactly-at-limit entry from an oversized one.
        let mut bytes = Vec::new();
        let limit = self.max_entry_bytes.saturating_add(1);
        if file.take(limit).read_to_end(&mut bytes).is_err()
            || u64::try_from(bytes.len()).is_ok_and(|length| length > self.max_entry_bytes)
        {
            self.record(|stats| stats.rejected += 1);
            return None;
        }
        let Some(program) = decode_entry(&bytes, world.fingerprint) else {
            self.record(|stats| stats.rejected += 1);
            return None;
        };
        self.record(|stats| stats.hits += 1);
        Some(program)
    }

    /// Persist already-verified canonical program bytes. The entry becomes
    /// visible only through the atomic host-output boundary.
    pub fn store(
        &self,
        world: &NormalizedInputWorld,
        program: &VerifiedVmProgram,
    ) -> Result<(), ArtifactCacheStoreError> {
        let entry = encode_entry(world.fingerprint, program);
        let found = u64::try_from(entry.len()).expect("cache entry length exceeds u64");
        if found > self.max_entry_bytes {
            return Err(ArtifactCacheStoreError::EntryTooLarge {
                found,
                limit: self.max_entry_bytes,
            });
        }
        fs::create_dir_all(&self.root).map_err(|source| ArtifactCacheStoreError::Io {
            path: self.root.clone(),
            source,
        })?;
        let path = self.entry_path(world.fingerprint);
        write_atomically(&path, &entry).map_err(|error| match error {
            crate::AtomicWriteError::InvalidTarget { path } => ArtifactCacheStoreError::Io {
                path,
                source: io::Error::new(io::ErrorKind::InvalidInput, "invalid cache entry path"),
            },
            crate::AtomicWriteError::Io { path, source } => ArtifactCacheStoreError::Io { path, source },
        })?;
        self.record(|stats| stats.stores += 1);
        Ok(())
    }

    fn entry_path(&self, world: Digest) -> PathBuf {
        self.root.join(format!("{world}.g0ac"))
    }

    fn record(&self, update: impl FnOnce(&mut ArtifactCacheStats)) {
        update(
            &mut *self
                .stats
                .lock()
                .expect("artifact cache stats mutex poisoned"),
        );
    }
}

fn encode_entry(world: Digest, program: &VerifiedVmProgram) -> Vec<u8> {
    let program_bytes = program.canonical_bytes();
    let mut bytes = Vec::with_capacity(ENVELOPE_BYTES + program_bytes.len());
    bytes.extend_from_slice(&CACHE_MAGIC);
    bytes.extend_from_slice(&STAGE0_ARTIFACT_CACHE_SCHEMA.to_le_bytes());
    bytes.extend_from_slice(&world.as_bytes());
    bytes.extend_from_slice(&program.fingerprint().as_bytes());
    bytes.extend_from_slice(&Digest::of_bytes(&program_bytes).as_bytes());
    bytes.extend_from_slice(&(program_bytes.len() as u64).to_le_bytes());
    bytes.extend_from_slice(&program_bytes);
    bytes
}

fn decode_entry(bytes: &[u8], expected_world: Digest) -> Option<VerifiedVmProgram> {
    if bytes.len() < ENVELOPE_BYTES || bytes.get(0..8)? != CACHE_MAGIC {
        return None;
    }
    let schema = u32::from_le_bytes(bytes.get(8..12)?.try_into().ok()?);
    if schema != STAGE0_ARTIFACT_CACHE_SCHEMA {
        return None;
    }
    let world = Digest::from_bytes(bytes.get(12..44)?.try_into().ok()?);
    if world != expected_world {
        return None;
    }
    let fingerprint = Digest::from_bytes(bytes.get(44..76)?.try_into().ok()?);
    let checksum = Digest::from_bytes(bytes.get(76..108)?.try_into().ok()?);
    let length = u64::from_le_bytes(bytes.get(108..116)?.try_into().ok()?);
    let payload = bytes.get(ENVELOPE_BYTES..)?;
    if length != u64::try_from(payload.len()).ok()? || Digest::of_bytes(payload) != checksum {
        return None;
    }
    let program = decode_and_verify_program(payload).ok()?;
    (program.fingerprint() == fingerprint).then_some(program)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{collections::BTreeMap, sync::atomic::{AtomicU64, Ordering}};

    use crate::{
        CompilationMode, CompilationRequest, CompilerBuildIdentity, LogicalPath, PackageKey,
        SourceInput, StageZeroCompiler,
    };

    static NEXT_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    fn temporary_directory() -> PathBuf {
        let ordinal = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "grandiose-stage0-artifact-cache-{}-{ordinal}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        directory
    }

    fn request(source: &str) -> CompilationRequest {
        let package = PackageKey("cache-test@0.1.0".into());
        CompilationRequest {
            build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"artifact-cache-test")),
            mode: CompilationMode::Build,
            root_package: package.clone(),
            sources: vec![SourceInput::new(
                package,
                LogicalPath::parse("src/main.glorious").unwrap(),
                source.as_bytes(),
            )],
            target: "g1-vm".into(),
            semantic_options: BTreeMap::new(),
            codegen_options: BTreeMap::new(),
            capability_manifest: vec![],
            runtime_manifest: None,
        }
    }

    fn compile(request: CompilationRequest) -> VerifiedVmProgram {
        StageZeroCompiler::new()
            .compile(request)
            .unwrap()
            .artifact
            .unwrap()
    }

    #[test]
    fn persistent_artifact_cache_round_trips_verified_canonical_programs() {
        let directory = temporary_directory();
        let request = request("pub fn main() -> i64 { 42 }");
        let world = request.clone().normalize().unwrap();
        let program = compile(request);
        let cache = PersistentArtifactCache::new(&directory);

        cache.store(&world, &program).unwrap();
        let loaded = cache.load(&world).expect("verified cache hit");

        assert_eq!(loaded.canonical_bytes(), program.canonical_bytes());
        assert_eq!(loaded.run_i64().unwrap(), 42);
        assert_eq!(
            cache.stats(),
            ArtifactCacheStats {
                hits: 1,
                misses: 0,
                rejected: 0,
                stores: 1,
            }
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn persistent_artifact_cache_rejects_stale_and_corrupted_entries_as_misses() {
        let directory = temporary_directory();
        let first = request("pub fn main() -> i64 { 42 }");
        let first_world = first.clone().normalize().unwrap();
        let second_world = request("pub fn main() -> i64 { 43 }").normalize().unwrap();
        let cache = PersistentArtifactCache::new(&directory);
        cache.store(&first_world, &compile(first)).unwrap();

        assert!(cache.load(&second_world).is_none(), "different worlds cannot share an artifact key");
        let path = cache.entry_path(first_world.fingerprint);
        fs::write(path, b"forged cache entry").unwrap();
        assert!(cache.load(&first_world).is_none(), "corrupt entries are ignored before execution");
        assert_eq!(
            cache.stats(),
            ArtifactCacheStats {
                hits: 0,
                misses: 1,
                rejected: 1,
                stores: 1,
            }
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn compiler_artifact_cache_path_reuses_only_a_verified_exact_world() {
        let directory = temporary_directory();
        let request = request("pub fn main() -> i64 { 42 }");
        let cache = PersistentArtifactCache::new(&directory);

        let fresh = StageZeroCompiler::new()
            .compile_artifact_with_cache(request.clone(), &cache)
            .unwrap()
            .expect("build mode emits a program");
        let reused = StageZeroCompiler::new()
            .compile_artifact_with_cache(request, &cache)
            .unwrap()
            .expect("exact cached program");

        assert_eq!(fresh.canonical_bytes(), reused.canonical_bytes());
        assert_eq!(reused.run_i64().unwrap(), 42);
        assert_eq!(
            cache.stats(),
            ArtifactCacheStats {
                hits: 1,
                misses: 1,
                rejected: 0,
                stores: 1,
            }
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn persistent_artifact_cache_rejects_entries_larger_than_its_streaming_limit() {
        let directory = temporary_directory();
        let world = request("pub fn main() -> i64 { 42 }").normalize().unwrap();
        let limit = ENVELOPE_BYTES as u64;
        let cache = PersistentArtifactCache::with_max_entry_bytes(&directory, limit);
        fs::write(
            cache.entry_path(world.fingerprint),
            vec![0_u8; usize::try_from(limit + 1).unwrap()],
        )
        .unwrap();

        assert!(cache.load(&world).is_none());
        assert_eq!(cache.stats().rejected, 1);
        fs::remove_dir_all(directory).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn persistent_artifact_cache_rejects_symlinked_entries_before_opening_them() {
        use std::os::unix::fs::symlink;

        let directory = temporary_directory();
        let world = request("pub fn main() -> i64 { 42 }").normalize().unwrap();
        let external = directory.join("outside-cache-record");
        fs::write(&external, b"not a cache entry").unwrap();
        let cache = PersistentArtifactCache::new(&directory);
        symlink(&external, cache.entry_path(world.fingerprint)).unwrap();

        assert!(cache.load(&world).is_none());
        assert_eq!(cache.stats().rejected, 1);
        fs::remove_dir_all(directory).unwrap();
    }
}
