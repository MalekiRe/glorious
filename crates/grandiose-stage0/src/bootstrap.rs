//! Canonical bootstrap-world manifests and convergence checks.
//!
//! A self-hosting driver is intentionally outside the semantic service, but
//! the evidence it needs is not.  This module turns an accepted immutable
//! world and its independently verified artifact into a compact, path-free
//! manifest.  A later stage can compare those manifests without consulting a
//! checkout, a warm cache, or host process state.

use crate::{BootstrapLimits, BootstrapStage, Digest, NormalizedInputWorld, VerifiedVmProgram};
use crate::request::{put as append, put_runtime_manifest};

// Schema three rejects evidence using the ambiguous/unbound v1 input
// commitments. The manifest's field layout and VM artifact schema are unchanged.
pub const BOOTSTRAP_MANIFEST_SCHEMA: u32 = 3;
pub const BOOTSTRAP_MANIFEST_MAGIC: [u8; 8] = *b"G0BM\r\n\x1a\n";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BootstrapManifest {
    pub schema: u32,
    pub stage: BootstrapStage,
    /// Exact accepted request-world identity, including producer identity.
    pub world: Digest,
    /// Inputs that determine the meaning of the compiler source bundle.
    pub source_semantics: Digest,
    /// Inputs that determine emitted code and its runtime authority.
    pub codegen: Digest,
    /// Canonical verified VM program identity.
    pub artifact: Digest,
    /// Digest of the exact canonical bytes independently verified before the
    /// program became executable. This is deliberately distinct from the
    /// semantic program fingerprint: stage-two/stage-three convergence is a
    /// byte-identity contract, including the released envelope/schema.
    pub artifact_bytes: Digest,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BootstrapConvergenceError {
    UnsupportedSchema { found: u32 },
    InvalidStage { ordinal: u32, reason: &'static str },
    StageOrderMismatch { earlier: u32, later: u32 },
    ProducerMismatch { expected: Digest, found: Digest },
    SourceWorldMismatch { left: Digest, right: Digest },
    CodegenInputMismatch { left: Digest, right: Digest },
    ArtifactMismatch { left: Digest, right: Digest },
    ArtifactBytesMismatch { left: Digest, right: Digest },
}

/// Compatibility evidence for attaching a decoded bootstrap manifest to an
/// independently decoded and verified compiler artifact.  A manifest carries
/// commitments, not an ambient handle to executable bytes; the driver must
/// make this check before treating it as seed or predecessor provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BootstrapArtifactCompatibilityError {
    InvalidManifest(BootstrapManifestError),
    ArtifactMismatch { expected: Digest, found: Digest },
    ArtifactBytesMismatch { expected: Digest, found: Digest },
}

/// A manifest is small fixed-shape evidence, but it may still cross an
/// untrusted process boundary. Decode failures are deliberately distinct from
/// convergence failures so a driver cannot mistake corrupt evidence for a
/// genuine stage disagreement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BootstrapManifestError {
    Truncated,
    InvalidMagic,
    UnsupportedSchema { found: u32 },
    InvalidStage { reason: &'static str },
    InvalidExpectedArtifactTag { found: u8 },
    TrailingBytes,
}

impl BootstrapManifest {
    pub fn from_verified_program(
        world: &NormalizedInputWorld,
        stage: BootstrapStage,
        artifact: &VerifiedVmProgram,
    ) -> Self {
        Self {
            schema: BOOTSTRAP_MANIFEST_SCHEMA,
            stage,
            world: world.fingerprint,
            source_semantics: source_semantics_fingerprint(world),
            codegen: codegen_fingerprint(world),
            artifact: artifact.fingerprint(),
            artifact_bytes: Digest::of_bytes(&artifact.canonical_bytes()),
        }
    }

    /// Compare adjacent stage products under the self-host convergence
    /// contract.  The later stage must be exactly the successor of this one
    /// and must name this verified artifact as its producer.  Producer and
    /// stage ordinal are intentionally absent from the byte-identity
    /// projection below, but they are essential provenance evidence: without
    /// this binding a forged or skipped manifest pair could claim convergence
    /// merely because two unrelated artifacts happened to be byte-identical.
    pub fn compare_convergence(&self, later: &Self) -> Result<(), BootstrapConvergenceError> {
        for manifest in [self, later] {
            if manifest.schema != BOOTSTRAP_MANIFEST_SCHEMA {
                return Err(BootstrapConvergenceError::UnsupportedSchema {
                    found: manifest.schema,
                });
            }
            if let Err(BootstrapManifestError::InvalidStage { reason }) = manifest.validate() {
                return Err(BootstrapConvergenceError::InvalidStage {
                    ordinal: manifest.stage.ordinal,
                    reason,
                });
            }
        }
        let expected_ordinal = self.stage.ordinal.checked_add(1).ok_or(
            BootstrapConvergenceError::StageOrderMismatch {
                earlier: self.stage.ordinal,
                later: later.stage.ordinal,
            },
        )?;
        if later.stage.ordinal != expected_ordinal {
            return Err(BootstrapConvergenceError::StageOrderMismatch {
                earlier: self.stage.ordinal,
                later: later.stage.ordinal,
            });
        }
        if later.stage.producer != self.artifact {
            return Err(BootstrapConvergenceError::ProducerMismatch {
                expected: self.artifact,
                found: later.stage.producer,
            });
        }
        if self.source_semantics != later.source_semantics {
            return Err(BootstrapConvergenceError::SourceWorldMismatch {
                left: self.source_semantics,
                right: later.source_semantics,
            });
        }
        if self.codegen != later.codegen {
            return Err(BootstrapConvergenceError::CodegenInputMismatch {
                left: self.codegen,
                right: later.codegen,
            });
        }
        if self.artifact != later.artifact {
            return Err(BootstrapConvergenceError::ArtifactMismatch {
                left: self.artifact,
                right: later.artifact,
            });
        }
        if self.artifact_bytes != later.artifact_bytes {
            return Err(BootstrapConvergenceError::ArtifactBytesMismatch {
                left: self.artifact_bytes,
                right: later.artifact_bytes,
            });
        }
        Ok(())
    }

    /// Bind this manifest to the actual verified artifact supplied by a seed
    /// store or predecessor stage.  Comparing manifests alone is insufficient
    /// after decoding hostile bytes: both commitments must match the exact
    /// canonical bytes which the VM verifier accepted.
    pub fn validate_verified_artifact(
        &self,
        artifact: &VerifiedVmProgram,
    ) -> Result<(), BootstrapArtifactCompatibilityError> {
        self.validate()
            .map_err(BootstrapArtifactCompatibilityError::InvalidManifest)?;
        let fingerprint = artifact.fingerprint();
        if self.artifact != fingerprint {
            return Err(BootstrapArtifactCompatibilityError::ArtifactMismatch {
                expected: self.artifact,
                found: fingerprint,
            });
        }
        let bytes = Digest::of_bytes(&artifact.canonical_bytes());
        if self.artifact_bytes != bytes {
            return Err(BootstrapArtifactCompatibilityError::ArtifactBytesMismatch {
                expected: self.artifact_bytes,
                found: bytes,
            });
        }
        Ok(())
    }

    /// Canonical, allocation-free manifest encoding. It contains no source
    /// paths, timestamps, or host state; the exact stage contract is retained
    /// so a decoded manifest cannot be reattached to weaker limits or a
    /// different producer by a later driver.
    pub fn encode(&self) -> Result<Vec<u8>, BootstrapManifestError> {
        self.validate()?;
        let mut output = Vec::with_capacity(254);
        output.extend_from_slice(&BOOTSTRAP_MANIFEST_MAGIC);
        output.extend_from_slice(&self.schema.to_le_bytes());
        output.extend_from_slice(&self.stage.ordinal.to_le_bytes());
        output.extend_from_slice(&self.stage.producer.as_bytes());
        output.push(self.stage.optimization_level);
        output.extend_from_slice(&self.stage.limits.max_sources.to_le_bytes());
        output.extend_from_slice(&self.stage.limits.max_total_source_bytes.to_le_bytes());
        match self.stage.expected_artifact {
            Some(expected) => {
                output.push(1);
                output.extend_from_slice(&expected.as_bytes());
            }
            None => output.push(0),
        }
        for digest in [
            self.world,
            self.source_semantics,
            self.codegen,
            self.artifact,
            self.artifact_bytes,
        ] {
            output.extend_from_slice(&digest.as_bytes());
        }
        Ok(output)
    }

    /// Decode and structurally validate one canonical bootstrap manifest.
    /// Callers still compare it to a separately verified artifact before using
    /// it as convergence evidence.
    pub fn decode(bytes: &[u8]) -> Result<Self, BootstrapManifestError> {
        let mut cursor = ManifestCursor { bytes, offset: 0 };
        let magic = cursor.array::<8>()?;
        if magic != BOOTSTRAP_MANIFEST_MAGIC {
            return Err(BootstrapManifestError::InvalidMagic);
        }
        let schema = u32::from_le_bytes(cursor.array()?);
        if schema != BOOTSTRAP_MANIFEST_SCHEMA {
            return Err(BootstrapManifestError::UnsupportedSchema { found: schema });
        }
        let ordinal = u32::from_le_bytes(cursor.array()?);
        let producer = Digest::from_bytes(cursor.array()?);
        let optimization_level = cursor.byte()?;
        let max_sources = u32::from_le_bytes(cursor.array()?);
        let max_total_source_bytes = u64::from_le_bytes(cursor.array()?);
        let expected_artifact = match cursor.byte()? {
            0 => None,
            1 => Some(Digest::from_bytes(cursor.array()?)),
            found => {
                return Err(BootstrapManifestError::InvalidExpectedArtifactTag { found });
            }
        };
        let stage = BootstrapStage {
            ordinal,
            producer,
            optimization_level,
            limits: BootstrapLimits::new(max_sources, max_total_source_bytes),
            expected_artifact,
        };
        validate_stage(&stage)?;
        let manifest = Self {
            schema,
            stage,
            world: Digest::from_bytes(cursor.array()?),
            source_semantics: Digest::from_bytes(cursor.array()?),
            codegen: Digest::from_bytes(cursor.array()?),
            artifact: Digest::from_bytes(cursor.array()?),
            artifact_bytes: Digest::from_bytes(cursor.array()?),
        };
        if cursor.offset != bytes.len() {
            return Err(BootstrapManifestError::TrailingBytes);
        }
        Ok(manifest)
    }

    pub fn validate(&self) -> Result<(), BootstrapManifestError> {
        if self.schema != BOOTSTRAP_MANIFEST_SCHEMA {
            return Err(BootstrapManifestError::UnsupportedSchema { found: self.schema });
        }
        validate_stage(&self.stage)
    }
}

struct ManifestCursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl ManifestCursor<'_> {
    fn byte(&mut self) -> Result<u8, BootstrapManifestError> {
        let value = *self
            .bytes
            .get(self.offset)
            .ok_or(BootstrapManifestError::Truncated)?;
        self.offset += 1;
        Ok(value)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], BootstrapManifestError> {
        let end = self
            .offset
            .checked_add(N)
            .ok_or(BootstrapManifestError::Truncated)?;
        let bytes = self
            .bytes
            .get(self.offset..end)
            .ok_or(BootstrapManifestError::Truncated)?;
        self.offset = end;
        bytes
            .try_into()
            .map_err(|_| BootstrapManifestError::Truncated)
    }
}

fn validate_stage(stage: &BootstrapStage) -> Result<(), BootstrapManifestError> {
    if stage.ordinal == 0 {
        return Err(BootstrapManifestError::InvalidStage {
            reason: "stage ordinal must be positive",
        });
    }
    if stage.optimization_level > 3 {
        return Err(BootstrapManifestError::InvalidStage {
            reason: "optimization level exceeds stage contract",
        });
    }
    if stage.limits.max_sources == 0 || stage.limits.max_total_source_bytes == 0 {
        return Err(BootstrapManifestError::InvalidStage {
            reason: "stage limits must be positive",
        });
    }
    if stage.ordinal == 1 && stage.expected_artifact.is_some() {
        return Err(BootstrapManifestError::InvalidStage {
            reason: "seed stage must not pin a predecessor artifact",
        });
    }
    if stage.ordinal > 1 {
        let Some(expected) = stage.expected_artifact else {
            return Err(BootstrapManifestError::InvalidStage {
                reason: "non-seed stages must pin their predecessor artifact",
            });
        };
        if expected != stage.producer {
            return Err(BootstrapManifestError::InvalidStage {
                reason: "non-seed producer must equal the pinned predecessor artifact",
            });
        }
    }
    Ok(())
}

fn source_semantics_fingerprint(world: &NormalizedInputWorld) -> Digest {
    let mut bytes = Vec::new();
    append(
        &mut bytes,
        b"grandiose-stage0-bootstrap-source-semantics-v2",
    );
    for generation in [
        world.build.language_generation,
        world.build.query_generation,
        world.build.interface_generation,
        world.build.cache_generation,
    ] {
        append(&mut bytes, &generation.to_le_bytes());
    }
    append(&mut bytes, world.root_package.0.as_bytes());
    append(&mut bytes, &(world.sources.len() as u64).to_le_bytes());
    for source in world.sources.iter() {
        append(&mut bytes, source.package.0.as_bytes());
        append(&mut bytes, source.logical_path.as_str().as_bytes());
        append(&mut bytes, &source.digest.as_bytes());
    }
    append(&mut bytes, &(world.semantic_options.len() as u64).to_le_bytes());
    for (key, value) in &world.semantic_options {
        append(&mut bytes, key.as_bytes());
        append(&mut bytes, value.as_bytes());
    }
    put_runtime_manifest(&mut bytes, world.runtime_manifest.as_ref());
    Digest::of_bytes(&bytes)
}

fn codegen_fingerprint(world: &NormalizedInputWorld) -> Digest {
    let mut bytes = Vec::new();
    append(&mut bytes, b"grandiose-stage0-bootstrap-codegen-v2");
    append(&mut bytes, world.target.as_bytes());
    append(&mut bytes, &(world.codegen_options.len() as u64).to_le_bytes());
    for (key, value) in &world.codegen_options {
        append(&mut bytes, key.as_bytes());
        append(&mut bytes, value.as_bytes());
    }
    append(&mut bytes, &(world.capability_manifest.len() as u64).to_le_bytes());
    for capability in world.capability_manifest.iter() {
        append(&mut bytes, capability.as_bytes());
    }
    append(&mut bytes, &world.build.bytecode_generation.to_le_bytes());
    append(&mut bytes, &world.build.verifier_generation.to_le_bytes());
    Digest::of_bytes(&bytes)
}

#[cfg(test)]
mod authority_tests {
    use super::*;
    use crate::{
        CompilationMode, CompilationRequest, CompilerBuildIdentity, LogicalPath,
        HostImportSelector, PackageKey, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput, SourceInput,
    };
    use std::collections::BTreeMap;

    fn request() -> CompilationRequest {
        let package = PackageKey("app@0.1.0".into());
        CompilationRequest {
            build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"authority-regression")),
            mode: CompilationMode::Check,
            root_package: package.clone(),
            sources: vec![SourceInput::new(
                package, LogicalPath::parse("src/main.glorious").unwrap(),
                b"main() { () }".as_slice(),
            )],
            target: "g1-vm".into(),
            semantic_options: BTreeMap::new(),
            codegen_options: BTreeMap::new(),
            capability_manifest: vec![],
            runtime_manifest: Some(RuntimeManifestInput {
                standard_library: PackageKey("std@0.1.0".into()),
                selectors: vec![PrimitiveSelector {
                    role: PrimitiveRole::IntCheckedDiv,
                    module_path: "crate".into(), name: "primitive".into(),
                }],
                literal_views: vec![], host_imports: vec![],
            }),
        }
    }

    #[test]
    fn bootstrap_source_semantics_distinguish_checked_division_from_float_addition() {
        let integer = request();
        let mut float = integer.clone();
        float.runtime_manifest.as_mut().unwrap().selectors[0].role =
            PrimitiveRole::parse_selector_name("f32-add").unwrap();
        assert_ne!(
            source_semantics_fingerprint(&integer.normalize().unwrap()),
            source_semantics_fingerprint(&float.normalize().unwrap()),
            "bootstrap convergence must bind the actual runtime role"
        );
    }

    #[test]
    fn bootstrap_source_semantics_commit_to_literal_view_selection() {
        use crate::{LiteralViewKind, LiteralViewSelector};
        let empty = request();
        let baseline = source_semantics_fingerprint(&empty.clone().normalize().unwrap());
        let mut input = empty;
        input.runtime_manifest.as_mut().unwrap().literal_views.push(LiteralViewSelector {
            kind: LiteralViewKind::Utf8, module_path: "crate".into(), name: "view".into(),
        });
        let original = source_semantics_fingerprint(&input.clone().normalize().unwrap());
        assert_ne!(baseline, original);
        for field in 0..3 {
            let mut changed = input.clone();
            let view = &mut changed.runtime_manifest.as_mut().unwrap().literal_views[0];
            match field { 0 => view.kind = LiteralViewKind::Octets, 1 => view.module_path = "crate::other".into(), _ => view.name = "renamed".into() }
            assert_ne!(original, source_semantics_fingerprint(&changed.normalize().unwrap()));
        }
    }

    #[test]
    fn bootstrap_codegen_frames_options_separately_from_capabilities() {
        let mut options = request();
        options.codegen_options.insert("aa".into(), "bb".into());
        let mut capabilities = options.clone();
        capabilities.codegen_options.clear();
        capabilities.capability_manifest = vec!["aa".into(), "bb".into()];
        assert_ne!(
            codegen_fingerprint(&options.normalize().unwrap()),
            codegen_fingerprint(&capabilities.normalize().unwrap()),
            "different codegen inputs must not attest convergence"
        );
    }

    #[test]
    fn bootstrap_source_semantics_bind_every_host_import_field() {
        let mut original = request();
        original.runtime_manifest.as_mut().unwrap().host_imports.push(HostImportSelector {
            module_path: "crate::io".into(), name: "read".into(),
            capability: "fs-read".into(), symbol: "read-file".into(),
        });
        let fingerprint = source_semantics_fingerprint(&original.clone().normalize().unwrap());
        for field in 0..5 {
            let mut changed = original.clone();
            let imports = &mut changed.runtime_manifest.as_mut().unwrap().host_imports;
            match field {
                0 => imports[0].module_path.push('x'),
                1 => imports[0].name.push('x'),
                2 => imports[0].capability.push('x'),
                3 => imports[0].symbol.push('x'),
                _ => imports.clear(),
            }
            assert_ne!(fingerprint, source_semantics_fingerprint(&changed.normalize().unwrap()),
                "host input change {field} must change the source commitment");
        }
    }

    #[test]
    fn bootstrap_source_semantics_bind_semantic_generations_not_producer_identity() {
        let original = request();
        let fingerprint = source_semantics_fingerprint(&original.clone().normalize().unwrap());
        for field in 0..4 {
            let mut changed = original.clone();
            match field {
                0 => changed.build.language_generation += 1,
                1 => changed.build.query_generation += 1,
                2 => changed.build.interface_generation += 1,
                _ => changed.build.cache_generation += 1,
            }
            assert_ne!(fingerprint, source_semantics_fingerprint(&changed.normalize().unwrap()),
                "semantic generation {field} must change the source commitment");
        }
        let mut successor = original;
        successor.build.compiler = Digest::of_bytes(b"successor-compiler");
        assert_eq!(fingerprint, source_semantics_fingerprint(&successor.normalize().unwrap()),
            "adjacent producers may converge under the same semantic contract");
    }

    #[test]
    fn bootstrap_manifest_rejects_the_previous_commitment_schema() {
        assert_eq!(BOOTSTRAP_MANIFEST_SCHEMA, 3);
        let digest = Digest::of_bytes(b"schema-regression");
        let manifest = BootstrapManifest {
            schema: BOOTSTRAP_MANIFEST_SCHEMA,
            stage: BootstrapStage {
                ordinal: 1, producer: digest, optimization_level: 2,
                limits: BootstrapLimits::new(1, 1024), expected_artifact: None,
            },
            world: digest, source_semantics: digest, codegen: digest,
            artifact: digest, artifact_bytes: digest,
        };
        let mut bytes = manifest.encode().unwrap();
        assert_eq!(BootstrapManifest::decode(&bytes).unwrap(), manifest);
        bytes[8..12].copy_from_slice(&2_u32.to_le_bytes());
        assert_eq!(BootstrapManifest::decode(&bytes), Err(BootstrapManifestError::UnsupportedSchema { found: 2 }));
        let mut old = manifest;
        old.schema = 2;
        assert_eq!(old.encode(), Err(BootstrapManifestError::UnsupportedSchema { found: 2 }));
        assert_eq!(old.compare_convergence(&old), Err(BootstrapConvergenceError::UnsupportedSchema { found: 2 }));
    }
}
