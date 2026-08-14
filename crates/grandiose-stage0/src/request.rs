use std::{collections::BTreeMap, fmt, sync::Arc};

use crate::{
    identity::{Digest, FileKey, PackageKey},
    runtime_manifest::RuntimeManifestInput,
};

/// The deterministic constraints carried by a self-hosting compiler stage.
///
/// These are deliberately request data rather than ambient driver settings: a
/// bootstrap artifact must say which producer made it, the optimization level
/// used to make it, and the bounds under which its source world was accepted.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BootstrapStage {
    /// The first Rust-hosted build is stage one.  Later stages must use a
    /// strictly positive, monotonically named stage identity.
    pub ordinal: u32,
    /// Canonical identity of the compiler executable or seed artifact that
    /// produced this stage.
    pub producer: Digest,
    /// The fixed optimization level for this bootstrap invocation.
    pub optimization_level: u8,
    /// Explicit hostile-input bounds for the stage input world.
    pub limits: BootstrapLimits,
    /// Optional canonical artifact fingerprint from the immediately preceding
    /// stage.  When supplied, the emitted artifact must converge to it.
    pub expected_artifact: Option<Digest>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BootstrapLimits {
    pub max_sources: u32,
    pub max_total_source_bytes: u64,
}

impl BootstrapLimits {
    pub const fn new(max_sources: u32, max_total_source_bytes: u64) -> Self {
        Self {
            max_sources,
            max_total_source_bytes,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CompilationMode {
    Check,
    Build,
    Test,
    Inspect,
    Ide,
    Bootstrap(BootstrapStage),
}

/// Exact identity of semantics-affecting compiler generations. Presentation
/// versions intentionally do not appear here.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompilerBuildIdentity {
    pub compiler: Digest,
    pub language_generation: u32,
    pub query_generation: u32,
    pub interface_generation: u32,
    pub cache_generation: u32,
    pub bytecode_generation: u32,
    pub verifier_generation: u32,
}

/// The canonical Rust stage-zero generation values. Hosts with an independently
/// versioned compiler may construct `CompilerBuildIdentity` directly, but the
/// shipped stage-zero adapter must advance these whenever a corresponding
/// boundary product changes. Generation two records the schema-21 `Trap`
/// bytecode instruction and its verifier semantics. Generation three records
/// schema-22 nominal effect-instance arguments in `Perform`, which are part
/// of runtime handler identity. Generation six records schema-25 verified
/// one-shot deep handler frames, explicit forwarding, and continuation
/// cancellation. Cache generation two
/// records the total canonical ordering of recovered and open effect-row
/// types, which changes semantic-product fingerprints.
pub const STAGE0_LANGUAGE_GENERATION: u32 = 1;
pub const STAGE0_QUERY_GENERATION: u32 = 1;
pub const STAGE0_INTERFACE_GENERATION: u32 = 1;
pub const STAGE0_CACHE_GENERATION: u32 = 2;
pub const STAGE0_BYTECODE_GENERATION: u32 = 32;
pub const STAGE0_VERIFIER_GENERATION: u32 = 6;

impl CompilerBuildIdentity {
    /// Construct the complete generation identity for this Rust-hosted stage.
    /// The producer fingerprint remains host-supplied because it identifies
    /// the exact compiler executable or seed artifact, not its display name.
    pub const fn stage0(compiler: Digest) -> Self {
        Self {
            compiler,
            language_generation: STAGE0_LANGUAGE_GENERATION,
            query_generation: STAGE0_QUERY_GENERATION,
            interface_generation: STAGE0_INTERFACE_GENERATION,
            cache_generation: STAGE0_CACHE_GENERATION,
            bytecode_generation: STAGE0_BYTECODE_GENERATION,
            verifier_generation: STAGE0_VERIFIER_GENERATION,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LogicalPath(String);

impl LogicalPath {
    pub fn parse(path: impl Into<String>) -> Result<Self, InputError> {
        let path = path.into();
        if path.is_empty()
            || path.starts_with('/')
            || path.contains('\\')
            || path
                .split('/')
                .any(|segment| segment.is_empty() || segment == "." || segment == "..")
        {
            return Err(InputError::InvalidLogicalPath(path));
        }
        Ok(Self(path))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceInput {
    pub key: FileKey,
    pub package: PackageKey,
    pub logical_path: LogicalPath,
    pub bytes: Arc<[u8]>,
    pub digest: Digest,
}

impl SourceInput {
    pub fn new(
        package: PackageKey,
        logical_path: LogicalPath,
        bytes: impl Into<Arc<[u8]>>,
    ) -> Self {
        let bytes = bytes.into();
        Self {
            key: FileKey::new(&package, logical_path.as_str()),
            package,
            logical_path,
            digest: Digest::of_bytes(&bytes),
            bytes,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompilationRequest {
    pub build: CompilerBuildIdentity,
    pub mode: CompilationMode,
    pub root_package: PackageKey,
    pub sources: Vec<SourceInput>,
    pub target: String,
    pub semantic_options: BTreeMap<String, String>,
    pub codegen_options: BTreeMap<String, String>,
    pub capability_manifest: Vec<String>,
    /// Selectors for the finite primitive authority table. They are resolved
    /// against interfaces later, but their canonical form is world identity.
    pub runtime_manifest: Option<RuntimeManifestInput>,
}

/// Compiler-owned immutable input world. Every semantic query must be rooted
/// in one such world through a revision snapshot.
#[derive(Clone, Debug)]
pub struct NormalizedInputWorld {
    pub build: CompilerBuildIdentity,
    pub mode: CompilationMode,
    pub root_package: PackageKey,
    pub sources: Arc<[SourceInput]>,
    pub target: String,
    pub semantic_options: BTreeMap<String, String>,
    pub codegen_options: BTreeMap<String, String>,
    pub capability_manifest: Arc<[String]>,
    pub runtime_manifest: Option<RuntimeManifestInput>,
    pub fingerprint: Digest,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InputError {
    EmptySources,
    DuplicateFileKey(FileKey),
    DigestMismatch {
        file: FileKey,
        expected: Digest,
        actual: Digest,
    },
    SourceIdentityMismatch {
        supplied: FileKey,
        expected: FileKey,
    },
    InvalidUtf8(FileKey),
    InvalidLogicalPath(String),
    DuplicateCapability(String),
    InvalidCapability(String),
    InvalidRuntimeManifest,
    InvalidBootstrapStage {
        reason: &'static str,
    },
    BootstrapSourceLimit {
        actual: u64,
        limit: u64,
    },
}

impl fmt::Display for InputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptySources => write!(formatter, "the request contains no source inputs"),
            Self::DuplicateFileKey(key) => write!(formatter, "duplicate source identity: {key:?}"),
            Self::DigestMismatch {
                file,
                expected,
                actual,
            } => write!(
                formatter,
                "source digest mismatch for {file:?}: expected {expected}, got {actual}"
            ),
            Self::SourceIdentityMismatch { supplied, expected } => write!(
                formatter,
                "source identity mismatch: supplied {supplied:?}, expected {expected:?} from its package and logical path"
            ),
            Self::InvalidUtf8(file) => write!(formatter, "source {file:?} is not UTF-8"),
            Self::InvalidLogicalPath(path) => write!(formatter, "invalid logical path: {path}"),
            Self::DuplicateCapability(capability) => {
                write!(formatter, "duplicate capability: {capability}")
            }
            Self::InvalidCapability(capability) => {
                write!(formatter, "invalid capability: {capability}")
            }
            Self::InvalidRuntimeManifest => write!(formatter, "invalid runtime manifest input"),
            Self::InvalidBootstrapStage { reason } => {
                write!(formatter, "invalid bootstrap stage: {reason}")
            }
            Self::BootstrapSourceLimit { actual, limit } => write!(
                formatter,
                "bootstrap source input is {actual} bytes, exceeding its {limit}-byte limit"
            ),
        }
    }
}

impl std::error::Error for InputError {}

impl CompilationRequest {
    pub fn normalize(mut self) -> Result<NormalizedInputWorld, InputError> {
        if self.sources.is_empty() {
            return Err(InputError::EmptySources);
        }

        self.sources.sort_by(|left, right| {
            (&left.package, &left.logical_path, left.key).cmp(&(
                &right.package,
                &right.logical_path,
                right.key,
            ))
        });
        for source in &self.sources {
            let expected = FileKey::new(&source.package, source.logical_path.as_str());
            if source.key != expected {
                return Err(InputError::SourceIdentityMismatch {
                    supplied: source.key,
                    expected,
                });
            }
            let actual = Digest::of_bytes(&source.bytes);
            if actual != source.digest {
                return Err(InputError::DigestMismatch {
                    file: source.key,
                    expected: source.digest,
                    actual,
                });
            }
            if std::str::from_utf8(&source.bytes).is_err() {
                return Err(InputError::InvalidUtf8(source.key));
            }
        }
        for pair in self.sources.windows(2) {
            if pair[0].key == pair[1].key {
                return Err(InputError::DuplicateFileKey(pair[0].key));
            }
        }

        self.capability_manifest.sort();
        for capability in &self.capability_manifest {
            if capability.is_empty()
                || capability.contains('*')
                || capability.chars().any(char::is_whitespace)
            {
                return Err(InputError::InvalidCapability(capability.clone()));
            }
        }
        for pair in self.capability_manifest.windows(2) {
            if pair[0] == pair[1] {
                return Err(InputError::DuplicateCapability(pair[0].clone()));
            }
        }
        if let Some(manifest) = &mut self.runtime_manifest {
            manifest
                .canonicalize()
                .map_err(|_| InputError::InvalidRuntimeManifest)?;
        }
        if let CompilationMode::Bootstrap(stage) = &self.mode {
            validate_bootstrap_stage(stage, &self)?;
        }

        let fingerprint = fingerprint_world(&self);
        Ok(NormalizedInputWorld {
            build: self.build,
            mode: self.mode,
            root_package: self.root_package,
            sources: self.sources.into(),
            target: self.target,
            semantic_options: self.semantic_options,
            codegen_options: self.codegen_options,
            capability_manifest: self.capability_manifest.into(),
            runtime_manifest: self.runtime_manifest,
            fingerprint,
        })
    }
}

fn fingerprint_world(request: &CompilationRequest) -> Digest {
    let mut bytes = Vec::new();
    put(&mut bytes, b"grandiose-stage0-world-v1");
    put(&mut bytes, &request.build.compiler.as_bytes());
    for generation in [
        request.build.language_generation,
        request.build.query_generation,
        request.build.interface_generation,
        request.build.cache_generation,
        request.build.bytecode_generation,
        request.build.verifier_generation,
    ] {
        put(&mut bytes, &generation.to_le_bytes());
    }
    put(&mut bytes, &[mode_tag(&request.mode)]);
    if let CompilationMode::Bootstrap(stage) = &request.mode {
        put(&mut bytes, b"bootstrap-stage-v1");
        put(&mut bytes, &stage.ordinal.to_le_bytes());
        put(&mut bytes, &stage.producer.as_bytes());
        put(&mut bytes, &[stage.optimization_level]);
        put(&mut bytes, &stage.limits.max_sources.to_le_bytes());
        put(
            &mut bytes,
            &stage.limits.max_total_source_bytes.to_le_bytes(),
        );
        if let Some(expected) = stage.expected_artifact {
            put(&mut bytes, b"expected-artifact");
            put(&mut bytes, &expected.as_bytes());
        }
    }
    put(&mut bytes, request.root_package.0.as_bytes());
    put(&mut bytes, request.target.as_bytes());
    for source in &request.sources {
        put(&mut bytes, source.package.0.as_bytes());
        put(&mut bytes, source.logical_path.as_str().as_bytes());
        put(&mut bytes, &source.key.0.as_bytes());
        put(&mut bytes, &source.digest.as_bytes());
    }
    for (key, value) in &request.semantic_options {
        put(&mut bytes, key.as_bytes());
        put(&mut bytes, value.as_bytes());
    }
    for (key, value) in &request.codegen_options {
        put(&mut bytes, key.as_bytes());
        put(&mut bytes, value.as_bytes());
    }
    for capability in &request.capability_manifest {
        put(&mut bytes, capability.as_bytes());
    }
    if let Some(manifest) = &request.runtime_manifest {
        put(&mut bytes, b"runtime-manifest");
        put(&mut bytes, manifest.standard_library.0.as_bytes());
        for selector in &manifest.selectors {
            put(
                &mut bytes,
                &[match selector.role {
                    crate::PrimitiveRole::BranchBool => 0,
                    crate::PrimitiveRole::TextByteLen => 1,
                    crate::PrimitiveRole::TextConcat => 2,
                    crate::PrimitiveRole::TextEq => 3,
                    crate::PrimitiveRole::TextFromUtf8Checked => 4,
                    crate::PrimitiveRole::TextAsBytes => 5,
                    crate::PrimitiveRole::CharFromU32Checked => 6,
                    crate::PrimitiveRole::CharToU32 => 7,
                    crate::PrimitiveRole::BytesLen => 8,
                    crate::PrimitiveRole::BytesConcat => 9,
                    crate::PrimitiveRole::BytesGet => 10,
                    crate::PrimitiveRole::BytesSlice => 11,
                    crate::PrimitiveRole::BytesFromArrayMove => 12,
                    crate::PrimitiveRole::BytesToArray => 13,
                    crate::PrimitiveRole::BytesUtf8ValidUpTo => 14,
                    crate::PrimitiveRole::U32CheckedAdd => 15,
                    crate::PrimitiveRole::U32CheckedSub => 16,
                    crate::PrimitiveRole::U32CheckedMul => 17,
                    crate::PrimitiveRole::U32CheckedDiv => 18,
                    crate::PrimitiveRole::U32CheckedRem => 19,
                    crate::PrimitiveRole::U32WrappingAdd => 20,
                    crate::PrimitiveRole::U32WrappingSub => 21,
                    crate::PrimitiveRole::U32WrappingMul => 22,
                    crate::PrimitiveRole::U32WrappingShl => 23,
                    crate::PrimitiveRole::U32WrappingShr => 24,
                    crate::PrimitiveRole::U32CheckedShl => 25,
                    crate::PrimitiveRole::U32CheckedShr => 26,
                    crate::PrimitiveRole::U32Eq => 27,
                    crate::PrimitiveRole::U32Lt => 28,
                    crate::PrimitiveRole::U32Le => 29,
                    crate::PrimitiveRole::U32ToUsize => 30,
                    crate::PrimitiveRole::UsizeToU32Checked => 31,
                    crate::PrimitiveRole::IntCheckedAdd => 32,
                    crate::PrimitiveRole::IntWrappingAdd => 33,
                    crate::PrimitiveRole::IntConvertCheckedToI64 => 45,
                    crate::PrimitiveRole::IntConvertWrappingToI64 => 46,
                    crate::PrimitiveRole::IntConvertCheckedToU32 => 47,
                    crate::PrimitiveRole::IntConvertWrappingToU32 => 48,
                    crate::PrimitiveRole::IntConvertCheckedToUsize => 49,
                    crate::PrimitiveRole::IntConvertWrappingToUsize => 50,
                    crate::PrimitiveRole::IntConvertCheckedToU8 => 51,
                    crate::PrimitiveRole::IntConvertWrappingToU8 => 52,
                    crate::PrimitiveRole::IntConvertCheckedToU16 => 53,
                    crate::PrimitiveRole::IntConvertWrappingToU16 => 54,
                    crate::PrimitiveRole::IntWrappingSub => 35,
                    crate::PrimitiveRole::IntWrappingMul => 36,
                    crate::PrimitiveRole::IntEqual => 34,
                    crate::PrimitiveRole::IntLess => 38,
                    crate::PrimitiveRole::IntGreater => 39,
                    crate::PrimitiveRole::IntBitAnd => 37,
                    crate::PrimitiveRole::IntBitOr => 40,
                    crate::PrimitiveRole::IntBitXor => 41,
                    crate::PrimitiveRole::IntBitNot => 42,
                    crate::PrimitiveRole::IntShr => 44,
                    crate::PrimitiveRole::IntShl => 43,
                }],
            );
            put(&mut bytes, selector.module_path.as_bytes());
            put(&mut bytes, selector.name.as_bytes());
        }
    }
    Digest::of_bytes(&bytes)
}

fn mode_tag(mode: &CompilationMode) -> u8 {
    match mode {
        CompilationMode::Check => 0,
        CompilationMode::Build => 1,
        CompilationMode::Test => 2,
        CompilationMode::Inspect => 3,
        CompilationMode::Ide => 4,
        CompilationMode::Bootstrap(_) => 5,
    }
}

fn validate_bootstrap_stage(
    stage: &BootstrapStage,
    request: &CompilationRequest,
) -> Result<(), InputError> {
    if stage.ordinal == 0 {
        return Err(InputError::InvalidBootstrapStage {
            reason: "stage ordinal must be positive",
        });
    }
    if stage.optimization_level > 3 {
        return Err(InputError::InvalidBootstrapStage {
            reason: "optimization level must be in the range 0..=3",
        });
    }
    if stage.limits.max_sources == 0 || stage.limits.max_total_source_bytes == 0 {
        return Err(InputError::InvalidBootstrapStage {
            reason: "source limits must be positive",
        });
    }
    // The producer is not merely descriptive manifest text: it names the
    // exact compiler executable which accepted this request world. Keeping it
    // equal to the build identity prevents a stage from claiming seed or
    // predecessor provenance while actually running a different compiler.
    if stage.producer != request.build.compiler {
        return Err(InputError::InvalidBootstrapStage {
            reason: "bootstrap producer must match compiler build identity",
        });
    }
    if stage.ordinal == 1 && stage.expected_artifact.is_some() {
        return Err(InputError::InvalidBootstrapStage {
            reason: "seed stage must not pin a predecessor artifact",
        });
    }
    if stage.ordinal > 1 {
        let Some(expected) = stage.expected_artifact else {
            return Err(InputError::InvalidBootstrapStage {
                reason: "non-seed stages must pin their predecessor artifact",
            });
        };
        if expected != stage.producer {
            return Err(InputError::InvalidBootstrapStage {
                reason: "non-seed producer must equal the pinned predecessor artifact",
            });
        }
    }
    if request.sources.len() > stage.limits.max_sources as usize {
        return Err(InputError::InvalidBootstrapStage {
            reason: "source count exceeds bootstrap source limit",
        });
    }
    let total = request
        .sources
        .iter()
        .try_fold(0_u64, |total, source| {
            total.checked_add(source.bytes.len() as u64)
        })
        .ok_or(InputError::InvalidBootstrapStage {
            reason: "total source byte count overflows u64",
        })?;
    if total > stage.limits.max_total_source_bytes {
        return Err(InputError::BootstrapSourceLimit {
            actual: total,
            limit: stage.limits.max_total_source_bytes,
        });
    }
    if let Some(option) = request.codegen_options.get("optimization-level")
        && option != &stage.optimization_level.to_string()
    {
        return Err(InputError::InvalidBootstrapStage {
            reason: "codegen optimization-level disagrees with the bootstrap stage",
        });
    }
    Ok(())
}

fn put(output: &mut Vec<u8>, value: &[u8]) {
    output.extend_from_slice(&(value.len() as u64).to_le_bytes());
    output.extend_from_slice(value);
}
