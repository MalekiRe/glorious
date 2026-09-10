use std::{collections::{BTreeMap, BTreeSet}, fmt, sync::Arc};

use crate::{
    identity::{Digest, FileKey, PackageKey, package_module_alias},
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
/// types, which changes semantic-product fingerprints. Cache generation
/// three separates the checked-integer-division runtime authority tag from
/// f32 addition in request, bound-manifest, and bootstrap fingerprints.
/// Cache generation four records explicitly framed request/bootstrap input
/// collections and complete bootstrap runtime-authority commitments.
/// Language/interface generation two adds raw-pointer and unsafe contracts.
/// Cache generation five and verifier generation seven retain explicit unsafe
/// scopes and callable/implementation requirements through Core and MIR.
/// Cache seven, bytecode 50 and verifier nine add explicit unsafe reference
/// origins and frame-neutral native references over raw storage.
/// Cache eight instantiates conditional principal ownership and forwards
/// bounded quantity binders for source-defined zero-sized ownership markers.
/// Cache nine, bytecode 51 and verifier ten add native reference residents,
/// unsafe aggregate-reference origins and native/static address leaves.
/// Cache ten, bytecode 52 and verifier eleven migrate collection storage to
/// source, fix trait-body instance discovery and add explicit unsafe forgetting.
/// Cache eleven, bytecode 53 and verifier twelve remove retired collection and
/// static-view instructions and make the remaining Array element borrow shared-only.
/// Language/interface three and cache twelve add direct inherent functions,
/// their lexical Self/generic contracts, and type-owned member resolution.
/// Cache thirteen aligns borrowed trait receivers across Core and executable
/// instances and preserves scoped enum payload projection authority.
/// Cache fourteen adds body-local constructor lifetime inference and union
/// caller-loan provenance. Bytecode 54 and verifier thirteen add concrete
/// destruction glue and explicit projected/resident initialization state.
/// Cache fifteen records owned-pattern/reference transfers and selected-variant
/// destructor loans. Bytecode 55 and verifier fourteen delimit resumption
/// completion and preserve live source allocations across restored frames.
/// Cache sixteen preserves unsafe/external result loans through reborrowing.
/// Bytecode 56 and verifier fifteen retain source callable and nominal-field
/// contracts for capability-bound native linking before region erasure.
/// Cache seventeen, bytecode 57 and verifier sixteen select native storage
/// homes for addressable source locals and the corresponding resource contract.
/// Cache eighteen, bytecode 58 and verifier seventeen retain owned native
/// argument/result storage through synchronous native callbacks (native ABI 2).
/// Cache nineteen, bytecode 59 and verifier eighteen retain selected native
/// destruction operations and fix lexical cleanup after declined root probes.
/// Cache twenty, bytecode 60 and verifier nineteen retain callable capture
/// destruction and restore residual capture storage across invocations.
/// Cache twenty-one, bytecode 61 and verifier twenty seal frame destruction
/// obligations independently of a particular return or cancellation lowerer.
/// Bytecode 62 applies those obligations to abandoned dynamic-label frames
/// and resolves specialized label destinations by their executing definition.
/// Cache twenty-two and bytecode 63 preserve unresolved result inference at
/// bottom branches and explicit non-returning value-CFG paths, including
/// strict callee ordering and normal returns from label helpers.
/// Bytecode 64 extends abandonment cleanup to retained handler branches and
/// preserves terminal cancellation-clause control flow.
/// Language/interface four and cache twenty-three retain module opt-outs and
/// source-selected default preludes in lexical resolution and interface identity.
/// Cache twenty-four cancels provably unused optional resumption tokens at
/// clause exit, using the existing checked cancellation and cleanup protocol.
/// Cache twenty-five and verifier twenty-one separate deep resumption return
/// contexts and audit every suspended suffix reaching a shared clause.
/// Cache twenty-six checks pattern binder uniqueness after constant resolution.
/// Cache twenty-seven elaborates empty tuple syntax against the Unit type.
/// Cache twenty-eight diagnoses concrete floating literal overflow in Core.
/// Cache twenty-nine includes normal-completion transformations in returning
/// resumption contracts and keeps their result type distinct from the computation.
/// Interface five and cache thirty retain module-scoped field authority,
/// admit `pub` fields, and allow source-owned scalar inherent functions.
/// Cache thirty-one preserves captured callable resident contracts and checks
/// immediately applied compact closures using argument-provided type evidence.
/// Cache thirty-two releases vacated reference-carrier loans after their
/// provenance has been transferred to a new lexical binding.
/// It also gives inherent methods their unqualified source implicit label.
/// Canceled indirect calls account for entry into the callee without assuming
/// that callable arguments were invoked before cancellation.
/// Lifted closures preserve their own frozen safety qualifier.
/// Direct lexical resumption aliases retain their closure-escape restriction.
/// Cache thirty-three records contextual numeric literal constraints and
/// resolves existing expected-type substitutions before choosing a literal type.
/// Cache thirty-four includes the normal-completion path in handler callable
/// use summaries unless direct operation dispatch has been established.
/// Cache thirty-five shares structural coverage with that dispatch proof and
/// fuses proven immediate, continuation-only closure invocations in scope.
/// Ordinary `resume` bindings take precedence over its migration shorthand.
/// Cache thirty-six enforces explicit mutable local binding authority for
/// assignment and unique borrowing, independently of referent mutability.
/// Cache thirty-seven checks explicit local type annotations and supplies
/// their types as initializer context without relaxing rigid lifetime bounds.
/// Cache thirty-eight admits checked numeric tuple value/place projections.
/// Cache thirty-nine admits irrefutable destructuring lets with a lexical
/// continuation, checked ownership transfer, and explicit binder mutability.
/// Cache forty requires zero-use permission for values discarded by a let
/// pattern and reserves distinct diagnostic codes for binding authority.
/// Cache forty-one independently rederives tuple value/place projection
/// arities and selected field types from their structural base layouts.
/// Cache forty-two admits associated effect-row union terms after `|` and
/// uses declared associated-item kinds for bare row definitions/defaults.
/// Cache forty-three and interface six retain independent effect-row union
/// operands; bytecode sixty-five/verifier twenty-two use their framed set
/// encoding and reject noncanonical untrusted operand sequences.
/// Cache forty-four distinguishes an absent module name from an existing
/// binding hidden behind a private import edge.
/// Cache forty-five retains mandatory tail sites through cleanup and runtime
/// lowering. Bytecode sixty-six/verifier twenty-three add checked consuming
/// activation transfers, independent of optional tail-call optimization.
/// Cache forty-six/interface seven retain scoped item/import/member visibility
/// and make record fields private by default under declaring-module authority.
/// Cache forty-seven/interface eight distinguish nominal tuple-struct layouts
/// and expose concrete struct constructors in the value namespace.
/// Cache forty-eight infers omitted nominal row and const arguments from
/// constructor payloads and contextual results instead of inventing defaults.
/// Bytecode sixty-seven/verifier twenty-four retain generic argument kinds
/// in nominal identities and their independently checked layout descriptors.
pub const STAGE0_LANGUAGE_GENERATION: u32 = 4;
pub const STAGE0_QUERY_GENERATION: u32 = 1;
pub const STAGE0_INTERFACE_GENERATION: u32 = 22;
// Integer const values and expressions retain kind, sign, and full magnitude;
// source range checks wait for the declared slot kind. Older identities and
// artifacts cannot be reinterpreted using the new canonical representation.
// Cache 58 checks scalar integer literals after inference and admits the
// directly constrained, immediately negated signed-minimum magnitude.
// Cache 59 substitutes trait-method lifetimes simultaneously and preserves
// implementation-owned lifetimes in Self and inserted generic arguments.
// Cache 60 checks tail carriers using post-NLL value provenance, including
// incoming borrows and assignment joins, instead of rejecting reference types.
// Cache 61 gives explicitly borrowed temporaries frozen storage/loan identity
// and propagates referent context through explicit borrow expressions.
// Cache 62 classifies associated row equalities through the resolved item
// contract, including inherited items and bare effect-row parameters, and
// unifies intrinsic Fn row equalities before permission minimization.
// Cache 63 shifts free bound regions in caller-owned generic arguments and
// selected Self types when specialization enters a callable binder scope.
// Cache 64/interface 13 retain lifetime-quantified predicate bundles across
// frozen callable transformations and native source-contract fingerprints.
// Cache 65 checks lifetime-universal Fn predicates with fresh rigid regions
// and transactional leak checks instead of rejecting all quantified bounds.
// Cache 66 distinguishes omitted call-region inference from rigid enclosing
// lifetimes in structural callable values and explicit generic applications.
// Cache 67 infers explicit anonymous lifetime arguments and adds safe,
// address-only pointer equality/inspection to the finite memory authority.
// Cache 68 publishes inferred structural expression/place types before use
// and evaluates computed assignment capabilities in frozen loan analysis.
// Cache 69/verifier 30 reconstruct typed memory and independent-input helper
// preservation for mandatory-tail frame transfer.
// Cache 70/interface 14 preserve and prove implementation associated-item
// equalities, with body-local equality assumptions isolated from global rules.
// Cache 71 materializes expected shared reborrows, carries contextual type
// evidence across call regions, and normalizes impl contracts in lexical scope.
// Cache 72/verifier 32 prove that disposing a lexical label has no capture
// destructor, without making the live label a frame-independent tail carrier.
// Cache 73/interface 15 preserve stored reference paths, expected unique
// reborrows, and associated-item domains/result/outlives contracts. Verifier
// 33 audits exact local-label transfers and proves conditional preservation
// for executable higher-order callbacks independently of their destruction.
// Cache 74/interface 16 and bytecode 71 preserve fixed-array identity/lengths
// and sparse array pattern indices. Verifier 34 checks their native layout
// overflow and the changed schema-115 pattern encoding independently.
// Cache 75/interface 17 retain lifetime-universal implementation predicates
// and prove user-trait bounds in isolated, budgeted lexical universes.
// Cache 76/interface 18 preserve nominal declaration predicates and enforce
// their instantiated domains; minimum-use checks retain every ordinary owner
// through scopes, branches and cancellation, with exact lexical evidence.
// Cache 77 protects conditionally selected destructor shells after freezing
// and normalizes rigid structural projections under exact lexical evidence.
// Cache 78 retains an explicit checked availability-release operation rather
// than erasing its lexical Environment/affine evidence into a discarded value.
// Cache 79 preserves lawful generic release through consuming disposal;
// verifier 35 rejects unsealed availability layouts at executable admission.
// It also retains bounded fixed-array reference paths and normalizes selected
// GAT item lifetime holes before contextual argument matching.
// Cache 80/interface 19 retain explicit position-specific operator targets,
// their declaring-scope resolution and target contracts in fixity keys.
// Cache 81 reserved the callable-contract lane, integrated at 88. Cache 82
// retains every conjunct in a `where T: A + B` bound rather than ignoring B.
// Cache 83 preserves identity unique-reference tail results through joins
// and introduces the private mixed LLVM/VM mandatory-tail dispatcher (ABI 5).
// Cache 84 pins static literal sites and admits exact shared byte-view slots
// (native ABI 4 / LLVM ABI 6), with checked heterogeneous enum projections.
// Cache 85 retains logical resident regions in generic source-managed owners.
// Cache 86 separates branded ownership continuations; cache 87 adds exact
// native floating conversions with an explicitly guarded machine profile.
// Cache 88/interface 20 retain callable environment/access/residual contracts,
// prove borrowed quantified Fn/RunsIn predicates and their exact associated
// equalities, and account for borrowed-call cancellation. Bytecode 72/schema
// 116 encode receiver authority; verifier 36 reconstructs it from executable
// capture accesses and invokes borrowed receivers through their original loan.
// Cache 89 establishes and restores the target's floating-point environment
// at bytecode entries and every admitted host/native callback boundary.
// Cache 90 preserves invariant-selected callable type arguments without
// freezing ordinary generic callback value joins.
// Cache 91 isolates literal decoding and the entire compilation pipeline
// from ambient floating-point controls and sticky exception status.
// Cache 92 retains complete callable capture footprints in logical owners
// and records implicit resident stores from captured invocation operands.
// Cache 93 preserves the continuation of a label whose bottom-typed body
// can transfer back to that label, including completion-arm rejoins.
// Cache 94 provides execution-domain callable residents in native raw storage.
// Native format 8 uses the same complete 40-byte callable layout.
// Cache 95 shares frozen continuation rules across semantic consumers and
// preserves transfers performed while evaluating another transfer's payload.
// Cache 96 shares capture formation rules and retains borrowed source slots
// together with the dependencies carried by nested captured values.
// Cache 97 shares explicit/captured invocation store rules and keeps capture
// containment distinct from aliasing the captured owner's stored residents.
// Cache 98 binds body-derived invocation outcomes to the shared continuation
// facts and keeps helper label exits separate from normal ownership joins.
// Cache 99 shares lexical label dependencies and rejects unfused first-class
// label captures at both source and independent Typed Core boundaries.
// Cache 100 retains label provenance in ordinary value/capture snapshots and
// checks outgoing values and stores at the label's own lexical boundary;
// shared invocation payloads also retain ordinary captured-input returns.
// Cache 101 retains positive invocation dependencies alongside unconditional
// coverage gaps; an unknown prefix is not proof of an empty result footprint.
// Cache 102 gives labels invariant generative nominal identity and retains
// that identity through semantic validation and invocation evidence.
// Cache 103 retains observed label-address obligations through callable inputs
// and lowers proven direct local-label callees after strict operand evaluation.
// Cache 104 erases resolved label proof carriers across checked runtime ABI
// components without rewriting nominal or effect-family identities.
// Cache 105 discharges staged lexical closure obligations by checked Core
// fusion and shares per-callable source loan products with escape/lowering.
// Cache 106 preserves exact handler/resumption binders through structural
// control fusion and independently validates the receiving lexical scopes.
// Cache 108 derives resumption capture/lifetime obligations from shared escape
// snapshots before fusion, replacing the source-only immediate-call rewrite.
// Cache 109 preserves factory-created capture dependencies and quantity
// identities through shared invocation results and value-based control fusion.
// Cache 110 binds generated callable residents to the checked native frame
// layouts and the existing execution-domain capture environment protocol.
// Cache 111 shares pattern inspection requirements and restores capture loans
// through the generated VM/native invocation contract and resident homes.
// Cache 112 authenticates complete returned-reference coverage through the
// shared explicit/captured invocation relation and resource input snapshots.
// Cache 113 transports reference identities with resident bytes and connects
// generated dereferences/patterns to their backing initialization contract.
// Cache 114 preserves returned loans of callable-owned capture storage.
// Cache 115/interface 21 retain effect-family and operation prerequisites,
// instantiate complete operation signatures and validate frozen applications.
// Cache 116 shares lexical, kinded projection normalization across signatures,
// Core and materialization, including mixed-kind cycles and callable binders.
// Cache 117 couples normal-result values and storage snapshots, preserves the
// handler computation's result loans and retains terminal operation payloads.
// Cache 118 retains known caller paths beside unresolved reference coverage,
// sharing one producer across declaration and realized invocation contracts.
// Cache 119 authenticates returned reference leaves independently of unrelated
// open result fields while preserving their complete conservative loan debt.
// Cache 120 separates retained reference loans from complete referent targets,
// including shared invocation may-stores and checked representation store edges.
// Cache 121 preserves proved absent reference payloads independently of
// missing targets, and binds evaluated initializer results to shared control.
// Cache 122 publishes writable reference slots independently of incoming loans
// and consumes positively proved read-only invocation/cleanup coverage.
// Cache 123 binds exact explicit/refinement borrow accesses to the typed
// resource input, independently of instantiated captured referent names.
// Cache 124/interface 22 preserve closed body-region identities, their
// directional constraints and local-storage bounds through capture contracts,
// validation and specialization. Runtime region representation is unchanged.
// Cache 125 checks strict computed field subjects through the same resource
// evaluation path as dereferenced and inspected subjects.
// Cache 126 retains inferred array literal extents and lets contextual octet
// literals supply u8 evidence to the ordinary Slice element inference cell.
// Cache 127 preserves trailing statement disposal and generated borrowed
// capture storage instead of copying its resident into a new owner.
// Cache 128 preserves empty and cyclic logical-region evidence and rigid
// generic result independence without fabricating reference validity.
// Cache 129 carries nested reference-result contents separately from the
// outer handle's lifetime debt and physical target authority.
// Cache 130 verifies mixed per-input frame-preservation requirements for
// calls borrowing local storage while transferring independent residents.
pub const STAGE0_CACHE_GENERATION: u32 = 130;
pub const STAGE0_BYTECODE_GENERATION: u32 = 72;
// Verifier 27 shares checked signed/radix pattern parsing and rounds f32
// patterns directly at f32 precision, without an intermediate f64 parse.
// Verifier 28 independently reconstructs frame-independence must facts and
// reference-result/mutation summaries from the executable call graph.
// Verifier 29 checks the exact safe signatures of address-only pointer leaves.
// Verifier 31 distinguishes independent reference contents from the local
// address of their carrier; overwrites invalidate retained referent proofs.
// Verifier 37 retains resumption identity in structural resident values,
// including field extraction, joins and exact handler expiry.
// Verifier 38 treats label payloads as parallel owned transfers, preserving
// resident provenance while retiring predecessor carriers before rejoin.
// Verifier 39 infers checked per-input whole-value/referent requirements
// through the executable call graph, including recursive helper summaries.
pub const STAGE0_VERIFIER_GENERATION: u32 = 39;

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
    InvalidPackageModuleAlias(PackageKey),
    DuplicatePackageModuleAlias {
        alias: String,
        first: PackageKey,
        second: PackageKey,
    },
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
            Self::InvalidPackageModuleAlias(package) => write!(
                formatter,
                "package `{}` cannot form a valid source module alias",
                package.0
            ),
            Self::DuplicatePackageModuleAlias {
                alias,
                first,
                second,
            } => write!(
                formatter,
                "packages `{}` and `{}` both normalize to source module alias `{alias}`",
                first.0, second.0
            ),
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

        // Source package bindings are semantic input, not a resolver
        // convenience. Validate the exact manifest-name to identifier bridge
        // before any module graph or interface product is published. This
        // makes `math-lib@…` available to source as `math_lib`, while two
        // distinct package identities that would claim the same source name
        // fail deterministically even if no body happens to import either.
        let packages = self
            .sources
            .iter()
            .map(|source| source.package.clone())
            .chain(std::iter::once(self.root_package.clone()))
            .collect::<BTreeSet<_>>();
        let mut aliases = BTreeMap::new();
        for package in packages {
            let alias = package_module_alias(&package)
                .ok_or_else(|| InputError::InvalidPackageModuleAlias(package.clone()))?;
            if let Some(first) = aliases.insert(alias.clone(), package.clone())
                && first != package
            {
                return Err(InputError::DuplicatePackageModuleAlias {
                    alias,
                    first,
                    second: package,
                });
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
    put(&mut bytes, b"grandiose-stage0-world-v2");
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
        put(&mut bytes, b"bootstrap-stage-v2");
        put(&mut bytes, &stage.ordinal.to_le_bytes());
        put(&mut bytes, &stage.producer.as_bytes());
        put(&mut bytes, &[stage.optimization_level]);
        put(&mut bytes, &stage.limits.max_sources.to_le_bytes());
        put(
            &mut bytes,
            &stage.limits.max_total_source_bytes.to_le_bytes(),
        );
        put(&mut bytes, &[u8::from(stage.expected_artifact.is_some())]);
        if let Some(expected) = stage.expected_artifact {
            put(&mut bytes, &expected.as_bytes());
        }
    }
    put(&mut bytes, request.root_package.0.as_bytes());
    put(&mut bytes, request.target.as_bytes());
    put(&mut bytes, &(request.sources.len() as u64).to_le_bytes());
    for source in &request.sources {
        put(&mut bytes, source.package.0.as_bytes());
        put(&mut bytes, source.logical_path.as_str().as_bytes());
        put(&mut bytes, &source.key.0.as_bytes());
        put(&mut bytes, &source.digest.as_bytes());
    }
    put(&mut bytes, &(request.semantic_options.len() as u64).to_le_bytes());
    for (key, value) in &request.semantic_options {
        put(&mut bytes, key.as_bytes());
        put(&mut bytes, value.as_bytes());
    }
    put(&mut bytes, &(request.codegen_options.len() as u64).to_le_bytes());
    for (key, value) in &request.codegen_options {
        put(&mut bytes, key.as_bytes());
        put(&mut bytes, value.as_bytes());
    }
    put(&mut bytes, &(request.capability_manifest.len() as u64).to_le_bytes());
    for capability in &request.capability_manifest {
        put(&mut bytes, capability.as_bytes());
    }
    put_runtime_manifest(&mut bytes, request.runtime_manifest.as_ref());
    Digest::of_bytes(&bytes)
}

// A sequence of length-prefixed values alone does not distinguish adjacent
// variable-length collections. Every list has a count and every optional
// section has a discriminator. Share the complete runtime input encoding with
// bootstrap commitments so authority fields cannot disappear in that projection.
pub(crate) fn put_runtime_manifest(bytes: &mut Vec<u8>, manifest: Option<&RuntimeManifestInput>) {
    put(bytes, &[u8::from(manifest.is_some())]);
    if let Some(manifest) = manifest {
        put(bytes, manifest.standard_library.0.as_bytes());
        put(bytes, &(manifest.selectors.len() as u64).to_le_bytes());
        for selector in &manifest.selectors {
            put(bytes, &[selector.role.stable_tag()]);
            put(bytes, selector.module_path.as_bytes());
            put(bytes, selector.name.as_bytes());
        }
        put(bytes, &(manifest.host_imports.len() as u64).to_le_bytes());
        for host in &manifest.host_imports {
            put(bytes, host.module_path.as_bytes());
            put(bytes, host.name.as_bytes());
            put(bytes, host.capability.as_bytes());
            put(bytes, host.symbol.as_bytes());
        }
    }
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

pub(crate) fn put(output: &mut Vec<u8>, value: &[u8]) {
    output.extend_from_slice(&(value.len() as u64).to_le_bytes());
    output.extend_from_slice(value);
}
