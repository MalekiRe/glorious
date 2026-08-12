import fs from 'node:fs';

const TARGET = process.argv[2] ?? 'docs/self-hosted-compiler/00-snowflake-synopsis-compendium.md';
const split = (text) => text.split('|').map((value) => value.trim()).filter(Boolean);
const section = (n, title, owner, concepts, operations, hazards, integrations, products, decisions) => ({
  n,
  title,
  owner,
  concepts: split(concepts),
  operations: split(operations),
  hazards: split(hazards),
  integrations: split(integrations),
  products: split(products),
  decisions: split(decisions),
});

const sections = [
  section(1, 'Architecture and Trust Boundaries',
    'the orchestration boundary, compiler service, verifier, supervisor, and VM',
    'CompilationRequest|CompilationOutcome|CompilerDatabase|CandidateArtifact|VerifiedArtifact|FrozenExecutionImage|CapabilityManifest|TrustDomain',
    'assemble request|execute semantic request|emit artifact|verify artifact|launch supervised VM|serve tooling query|classify boundary failure',
    'ambient filesystem access|conflated verification claims|VM acceptance of raw bytes|duplicated source semantics|spelling-based privilege|partial publication',
    'grand|grc CLI|compiler database|bytecode verifier|supervisor and language server',
    'normalized request|structured outcome|candidate artifact|verified execution image|trust manifest',
    'in-process service versus daemon|verifier process placement|future native backend boundary|remote-cache signing policy|final release trust base'),
  section(2, 'Compilation Inputs, Revisions, and Session Ownership',
    'CompilerDatabase and revision-qualified request, package, body, lowering, and emission sessions',
    'RawCompilationRequest|NormalizedInputWorld|RevisionRecord|DatabaseSnapshot|RequestSession|PackageSession|BodySession|EmissionSession',
    'normalize inputs|intern source blobs|create revision|pin snapshot|open request session|compile body|publish outputs|retire revision',
    'reopening source paths|mixing revisions|leaking local IDs|unbounded revision retention|stale publication|mandatory whole-program mutable AST',
    'typed query engine|stable identity system|dependency invalidation|persistent cache|frontend services',
    'input manifest|revision fingerprint|revision change set|publication batch|retention report',
    'revision granularity|editor overlay strategy|resource limits in fingerprints|source-blob deduplication|generation tagging'),
  section(3, 'The Typed Query Engine',
    'the CompilerDatabase query runtime',
    'QueryDescriptor|QueryKey|QueryFrame|QueryResult|DependencyEdge|MemoEntry|CyclePolicy|QueryTrace',
    'register query|demand query|read input leaf|validate memo|execute query|publish result|cancel query|explain recomputation',
    'dynamic type erasure|hidden dependencies|partial memo publication|recovered-value leakage|accidental query cycles|nondeterministic scheduling',
    'compilation revisions|stable identities|dependency invalidation|persistent caching|structured diagnostics',
    'query graph|result fingerprint|execution trace|query statistics|recompilation explanation',
    'single-threaded versus concurrent execution|effect-based demand versus explicit context|red-green validation algorithm|recovered result representation|cross-revision result sharing'),
  section(4, 'Stable Identity, Interning, and Typed Arenas',
    'database identity services and phase-local typed arena owners',
    'PackageKey|ModuleKey|DefKey|BodyKey|InstanceKey|StableSyntaxAnchor|InternedType|IdRange',
    'derive stable key|match identity across revisions|intern semantic value|allocate arena range|freeze and remap|decode persistent identity|inspect identity difference',
    'ordinal-based invalidation|raw integer identity confusion|source spans in semantic equality|identity collisions|stale generations|immortal interners',
    'revision model|frontend source model|typed query engine|persistent cache|tooling reference index',
    'identity map|canonical interner pool|local-to-persistent remap|collision report|identity-difference report',
    'anonymous identity algorithm|weak versus strong interning|persistent identity encoding|module path stability|identities for recovered syntax'),
  section(5, 'Dependency Tracking and Invalidation',
    'the typed query dependency journal and revision validator',
    'InputDependency|QueryDependency|SemanticFingerprint|PresentationFingerprint|DurabilityClass|ValidationState|InvalidationReason|ChangeJournal',
    'record dependency edge|compare direct input|validate dependency|mark result green|recompute red result|propagate semantic change|explain invalidation|audit dependency fanout',
    'hidden dependency edges|over-invalidation|under-invalidation|dependency cycles|semantic and span fingerprint conflation|file timestamp reliance',
    'typed query engine|revision records|stable identities|persistent cache|tooling explanations',
    'dependency graph|invalidation trace|fanout report|durability statistics|change explanation',
    'red-green validation details|edge granularity|diagnostic dependencies|fixity and implementation dependencies|use of host change hints'),
  section(6, 'Caching, Persistence, Eviction, and Schema Evolution',
    'compiler cache adapters under query-engine validation',
    'MemoryMemo|PersistentEntry|CacheKey|CacheSchema|ContentStore|ValidationEnvelope|EvictionPolicy|ArtifactCache',
    'look up memory memo|validate in-memory result|load persistent entry|decode and validate entry|recompute missing result|write entry atomically|evict retained value|quarantine corrupt entry',
    'cache treated as truth|incomplete cache keys|record corruption|nondeterministic serialization|stale schema reuse|unbounded cache growth',
    'typed queries|stable identities|deterministic serialization|artifact emission|optional remote cache',
    'cache manifest|entry validation envelope|content checksum|eviction log|warm-cold comparison',
    'which products to persist|compression format|remote entry signatures|reuse of verification products|memory eviction policy'),
  section(7, 'Determinism and Reproducibility',
    'every producer of externally visible compiler products',
    'DeterminismDomain|CanonicalOrder|StableFingerprint|FrozenPool|DeterministicWorklist|BuildManifest|ReproductionRecord|StageComparison',
    'canonicalize inputs|sort diagnostics|freeze canonical pools|order generic instances|run deterministic optimizer|serialize artifact|compare independent builds|report first divergence',
    'hash-map iteration leakage|wall-clock dependence|random-seed dependence|arena allocation order leakage|parallel scheduling races|absolute host path leakage',
    'all semantic phases|persistent caching|optimizer|artifact emission|bootstrap convergence',
    'build manifest|phase fingerprint set|divergence report|canonical remap|reproduction log',
    'stable hash function|logical path normalization|future concurrency discipline|diagnostic tie breaking|canonical instance ordering'),
  section(8, 'Cancellation, Resource Limits, Corruption Handling, and Security',
    'request sessions, query frames, defensive decoders, and publication guards',
    'CancellationToken|BudgetTree|ResourceLimit|PublicationGuard|CorruptionClass|QuarantineRecord|SecurityBoundary|FailureOutcome',
    'check cancellation|charge hierarchical budget|reserve memory|abort query frame|roll back publication|validate hostile input|quarantine external record|classify failure',
    'stack overflow|allocation amplification|stale result publication|failure-class conflation|hostile cache record|denial-of-service input',
    'typed query engine|input normalization|persistent cache|parser and solvers|bytecode verifier',
    'resource-limit report|cancellation trace|quarantine log|failure classification|security audit record',
    'cancellation polling frequency|budget inheritance|memory measurement strategy|recovery after invariant failure|fatal-process policy'),
  section(9, 'Source Model, Spans, Lossless Lexing, and Delimiter Pairing',
    'the frontend source service',
    'SourceBlob|FileSnapshot|SourceSpan|LineIndex|Token|Trivia|DelimiterMap|LexRecovery',
    'decode source|lex token stream|record trivia|pair delimiters|build line index|map editor position|incrementally relex|recover malformed token',
    'invalid UTF-8|nested comment overflow|delimiter storms|offset overflow|span drift|formatter lexer divergence',
    'normalized inputs|body parser|diagnostics|formatter|language server',
    'lossless token stream|delimiter map|line index|lexical diagnostics|round-trip proof',
    'UTF-8 policy|incremental relex window|trivia ownership|token identity across edits|line-ending normalization'),
  section(10, 'Packages, Modules, Structural Scanning, Interfaces, and Fixity',
    'the frontend package and interface service',
    'PackageGraph|ModuleTree|DeclarationShell|HeaderIndex|Visibility|FixityTable|DependencyInterface|ExportFingerprint',
    'construct module graph|scan declaration boundaries|collect headers|collect fixities|resolve module edges|build package interface|validate imported interface|fingerprint exports',
    'ambient file discovery|illegal module cycles|visibility leakage|fixity ordering errors|malformed dependency interface|private-change downstream invalidation',
    'grand orchestration|lossless source model|name resolution|trait and effect collection|persistent cache',
    'module outline|canonical package interface|export table|fixity map|module diagnostics',
    'external module layout|generic bodies in interfaces|re-export representation|module-cycle policy|public layout facts'),
  section(11, 'Body Parsing, Contextual Blocks, Operator Grouping, and Recovery',
    'the body-local frontend parsing service',
    'BodyTokenRange|TokenCursor|ParsedBody|ExprNode|PatternNode|OperatorStream|ContextualBlock|ParseCheckpoint',
    'enter body range|parse expression|parse pattern|collect flat operator stream|group by fixity|parse handler clause|recover syntax error|commit parser checkpoint',
    'exponential recovery|nonterminating parser loop|ambiguous contextual block|stale fixity use|unbounded recursion|duplicated parser implementations',
    'lossless source model|header and fixity collection|name resolution|formatter|IDE recovery',
    'body syntax arena|parse diagnostics|recovery map|grouped operator tree|syntax source map',
    'Pratt versus shunting-yard grouping|direct enum versus packed AST|body-level incremental parsing|recovery sentinel design|contextual trailing-block representation'),
  section(12, 'Name Resolution, Scopes, Visibility, and Reference Indexing',
    'the frontend resolution service',
    'ScopeMap|BindingId|ResolvedTarget|Namespace|ImportBinding|VisibilityContext|OccurrenceIndex|ResolutionRecovery',
    'enter lexical scope|declare binding|resolve local name|resolve module path|enforce visibility|resolve associated item shell|record occurrence|construct rename plan',
    'shadowing confusion|namespace collision|privacy leakage|ambiguous import|stale occurrence index|recovery misbinding',
    'module interfaces|body parser|type elaboration|language server|structured diagnostics',
    'resolved body|occurrence index|definition map|rename edit plan|ambiguity diagnostics',
    'separate resolution pass versus fused elaboration|scope journal representation|glob import policy|method lookup boundary|recovery binding policy'),
  section(13, 'Semantic Types, Normalization, and Inference',
    'the body-local static semantic service and canonical type interner',
    'SemanticType|InferenceVar|TypeScheme|ExpectedType|NormalizedType|TypeFacts|UnificationTable|TypeExplanation',
    'create inference variable|add type constraint|unify types|normalize alias|elaborate against expected type|zonk body term|intern complete type|explain mismatch',
    'occurs-check cycles|source spans in type equality|accidental coercion|unresolved inference variables|recursive normalization loops|inconsistent cached type facts',
    'trait solver|effect rows|quantity engine|borrow checker|Typed Core',
    'typed expression map|normalized type|memoized type facts|unification trace|type mismatch diagnostic',
    'coercion policy|never-type behavior|recursive alias rules|numeric defaulting|recovery type representation'),
  section(14, 'Generics, Traits, Associated Items, GATs, HRTBs, and Consts',
    'the canonical trait and generic solver',
    'GenericParam|CanonicalGoal|SolverTable|ImplCandidate|AssociatedProjection|Universe|ConstTerm|Evidence',
    'canonicalize goal|enumerate implementation candidates|check coherence|instantiate candidate|normalize associated projection|solve higher-ranked goal|evaluate structural const|construct evidence',
    'overlapping implementations|nonterminating solver cycle|universe leakage|const-evaluation explosion|unsound table reuse|ambiguous evidence',
    'semantic types|module interfaces|effect rows|quantity relations|generic instance discovery',
    'goal solution|proof tree|implementation index|projection normal form|coherence report',
    'specialization policy|negative reasoning boundary|auto-trait support|const evaluator scope|cross-package implementation indexing'),
  section(15, 'Effects, Effect Rows, Handlers, Resumptions, and Cancellation',
    'the static effect and control service',
    'EffectDecl|EffectInstance|EffectRow|OperationSig|HandlerType|ResumptionType|SuspensionPoint|CancellationPolicy',
    'collect effect declaration|infer effect row|type perform operation|select enclosing handler|type handler clause|capture continuation|type resume|type cancellation|propagate outward row',
    'unhandled effect escape|multishot unique capture|cancelling exact-positive continuation|handler ambiguity|incorrect deep reinstatement|reference payload lifetime escape',
    'semantic types|quantity engine|borrow checker|Typed Core|ownership MIR',
    'expression effect map|handler plan|resumption summary|outward effect row|effect diagnostics',
    'effect-row representation|finite resumption syntax|deep versus shallow handlers|partial-handler semantics|host-effect boundary'),
  section(16, 'Quantitative Use and Ownership Obligations',
    'the shared quantity kernel used by static checking, captures, resumptions, and PlaceFlow',
    'UseInterval|PrincipalUse|ActualUse|QuantityVar|UseEquation|MustMoveObligation|CopyObligation|ResumptionQuantity',
    'derive principal interval|add sequential uses|take branch hull|widen loop use|multiply nested execution|transfer owner|copy owner|check interval containment',
    'abandoning exact-positive owner|copy discharging original obligation|nonconvergent loop quantity|unauthorized private destruction|cancellation escape|continuation replay duplication',
    'effect system|borrow checker|PlaceFlow|Typed Core|diagnostic explanation',
    'quantity table|obligation graph|use derivation tree|containment result|final-use hint',
    'infinity representation|recursive principal intervals|quantity defaults|annotation requirements|diagnostic algebra presentation'),
  section(17, 'Regions, Lifetimes, Borrowing, and Reborrowing',
    'the shared region and borrow analysis over typed places',
    'RegionVar|OutlivesConstraint|Loan|Reborrow|Origin|Variance|SuspensionBoundary|DropCheck',
    'create region variable|borrow place|reborrow reference|propagate outlives|solve nonlexical regions|apply variance|check suspension crossing|validate destruction',
    'escaping reference|unique aliasing|loan across multishot capture|higher-ranked universe leak|partial move under active loan|destruction while borrowed',
    'semantic types|quantity obligations|callable captures|PlaceFlow|MIR validation',
    'region solution|loan graph|reference origin map|borrow diagnostic|suspension proof',
    'Polonius-like facts versus custom solver|region value representation|two-phase borrow support|references in effect payloads|borrow explanation format'),
  section(18, 'Callables, Captures, Brands, Environments, and Refinements',
    'the shared callable and nominal brand kernel',
    'CallableKind|CallableSignature|CaptureSet|CaptureMode|EnvironmentBrand|LabelBrand|RefinementEnv|RunsInEvidence',
    'collect callable shell|infer capture set|select capture modes|create fresh brand|type callable invocation|synthesize environment evidence|seal environment|lower callable',
    'parallel capture implementations|brand escape|receiver-mode mismatch|capture quantity mismatch|refinement fact leakage|replayed environment owner',
    'name resolution|semantic types|effects|quantity engine|Typed Core',
    'callable interface|capture layout|environment summary|brand table|call explanation',
    'single callable representation|capture inference phase|explicit move closure syntax|runtime erasure of labels|contextual block typing'),
  section(19, 'Typed Core',
    'the typed elaboration service and body-local Core builder',
    'CoreValue|CoreComputation|CoreCallable|CoreEffect|CoreHandler|CoreLabel|CoreEvidence|CoreSourceMap',
    'build Core value|bind computation|lower callable invocation|lower effect performance|lower handler|lower label transfer|validate Core|erase static evidence',
    'compiler-known source control node|duplicate persistent HIR|untyped Core payload|unresolved evidence|evaluation-order change|unmanifested host primitive',
    'typed elaboration|quantity checking|borrow checking|MIR lowering|control specialization',
    'Typed Core body|Core interface body|evidence table|Core source map|Core validation report',
    'administrative normal form|Core persistence policy|generic Core in dependency interfaces|pattern lowering point|evidence erasure timing'),
  section(20, 'PlaceFlow',
    'the shared sparse place-fact graph and fixed-point analyses',
    'Place|Projection|MovePath|InitializationState|UseSite|LoanFact|CaptureFact|CleanupObligation',
    'create root place|project subplace|record initialization|record use|propagate move state|attach loan fact|join predecessor states|derive cleanup obligation',
    'parallel ownership models|unsound control-flow join|partial-move confusion|cleanup fact divergence|continuation snapshot mismatch|syntax-based final-use guess',
    'quantity engine|borrow checker|MIR|optimizer|bytecode verification',
    'PlaceFlow graph|ownership state table|move map|cleanup plan|fact validation difference',
    'construction during Core or MIR|sparse storage representation|frontend fact import|loop fixed-point strategy|persistence boundary'),
  section(21, 'Ownership-and-Control MIR, Lowering, Cleanup, and Validation',
    'the MIR lowering service and checked MIR editor',
    'MirBody|Block|BlockParam|Local|Statement|Terminator|CleanupEdge|ControlSite',
    'lower Core body|create basic blocks|emit MIR statements|connect control edges|insert cleanup|encode handler and resumption|validate CFG and ownership|freeze MIR body',
    'implicit exceptional edge|incorrect cleanup insertion|evaluation-order change|block identity confusion|stale analysis after edit|unreachable-code semantic drift',
    'Typed Core|PlaceFlow|optimizer framework|function emitter|bytecode verifier',
    'raw MIR|validated MIR|MIR source map|cleanup map|CFG validation report',
    'SSA-like block parameters|explicit place representation|checked editor API|immediate abort semantics|guaranteed tail-call form'),
  section(22, 'Generic Instances, Monomorphization, and Interprocedural Summaries',
    'the instance discovery and specialization query family',
    'InstanceKey|Substitution|ReachabilityRoot|InstanceGraph|GenericBody|CallSummary|EffectSummary|OwnershipSummary',
    'canonicalize instance key|discover reachable instance|instantiate generic body|detect recursive SCC|compute summaries|cache instance MIR|enqueue callees|enforce instance budget',
    'monomorphization explosion|unstable substitution identity|recursive instance loop|cross-package generic mismatch|unsound call summary|hidden target dependency',
    'trait solver|Typed Core|MIR lowering|optimizer|dependency interfaces',
    'reachable instance set|instance graph|summary bundle|specialization report|instance-limit diagnostic',
    'monomorphization versus evidence passing|canonical substitution form|generic Core interface format|recursive instance handling|code sharing'),
  section(23, 'Optimizer Framework, Analyses, Budgets, and Invalidations',
    'the deterministic MIR optimizer and analysis manager',
    'OptimizationPipeline|AnalysisBundle|PassDescriptor|MirEditor|InvalidationMask|WorkBudget|ProfitModel|PassTrace',
    'request analysis bundle|run optimization pass|edit MIR transactionally|invalidate dependent analyses|validate transformation|iterate bounded fixed point|compare semantic traces|publish optimized MIR',
    'stale analysis reuse|nondeterministic pass order|illegal trap removal|unbounded optimizer work|pass interaction regression|lost source mapping',
    'validated MIR|PlaceFlow|typed query engine|determinism framework|diagnostic remarks',
    'optimized MIR|pass execution report|analysis cache|before-after difference|budget remark',
    'pass-manager architecture|optimization-level contents|validation frequency|interprocedural optimization scope|proof-carrying transformations'),
  section(24, 'Source-Defined Control Specialization',
    'the control summary analysis and structural optimizer',
    'ControlSummary|StaticCallable|ProofOnlyLabel|HandlerPlan|ResumptionPlan|LoopPlan|FusionBarrier|ControlExplanation',
    'analyze control helper|prove callable target|prove quantity legality|inline structural control|remove static handler|form direct loop|form direct leave|report residual machinery',
    'name-based special casing|unsound continuation replay|cleanup loss|avoidable closure allocation|residual dynamic handler lookup|opaque specialization failure',
    'standard library|Typed Core|MIR|optimizer framework|development diagnostics',
    'control plan|fusion explanation|machine-applicable lints|direct control CFG|residual machinery map',
    'control summary language|fallback behavior|lint thresholds|multishot specialization boundary|source mapping after fusion'),
  section(25, 'Register Allocation, Instruction Selection, and Function Emission',
    'the deterministic per-function emission service',
    'PhysicalRegister|RegisterClass|AddressablePlace|BlockLayout|EdgeTransfer|Instruction|FunctionFragment|SourcePcMap',
    'classify MIR value|allocate physical register|choose block layout|resolve parallel edge copies|select instruction|emit cleanup metadata|patch control targets|freeze function fragment',
    'type-unsafe register reuse|parallel-copy cycle corruption|cleanup-map mismatch|unstable block layout|incorrect target lowering|source-PC mapping drift',
    'optimized MIR|optimizer analyses|bytecode schema|emitted-fragment cache|bytecode verifier',
    'function fragment|register assignment map|relocation table|source-PC map|emission trace',
    'linear scan versus graph coloring|zero-sized register erasure|per-function cache granularity|block-order heuristic|cycle-break temporary policy'),
  section(26, 'Interface Artifacts, Executable Artifacts, Linking, and Serialization',
    'the canonical artifact encoder, decoder, and linker',
    'InterfaceArtifact|ExecutableArtifact|Section|CanonicalPool|SymbolRecord|LinkManifest|FeatureSet|CompatibilityVersion',
    'encode dependency interface|decode dependency interface|freeze canonical pools|link reachable functions|resolve symbols|write artifact sections|compute integrity digest|validate compatibility',
    'raw local ID serialization|ambiguous section layout|noncanonical pool order|unknown critical feature|duplicate symbol definition|ABI incompatibility',
    'package interfaces|generic instances|function emitter|bytecode verifier|grand build orchestration',
    'dependency interface file|GRBC executable|link manifest|checksum set|compatibility report',
    'interface filename and format|generic body payload|section schema evolution|incremental linking|backward-compatibility window'),
  section(27, 'Bytecode Decoder and Verifier',
    'the independent defensive artifact verifier',
    'Decoder|ArtifactView|VerificationState|RegisterState|OwnershipState|ControlState|CleanupState|FrozenExecutionImage',
    'decode artifact header|validate section table|verify type and signature records|run register dataflow|check move and copy legality|check control identities|check cleanup and captures|freeze execution image',
    'allocation amplification|hostile out-of-range index|unsound state merge|unchecked required feature|source-compiler trust leakage|mutable bytes after verification',
    'bytecode specification|deterministic emitter|VM loader|supervisor|hostile corpus and fuzzing',
    'verification report|frozen execution image|stable verifier error|state trace|hostile artifact corpus',
    'in-process versus separate verifier|verification-result caching|seeded development artifacts|function-level verification granularity|formal verifier model'),
  section(28, 'VM, Supervisor, Host Capabilities, and Runtime Limits',
    'the verified VM worker, supervisor process, and exact host adapters',
    'ExecutionFrame|RegisterFile|ArenaHandle|RuntimeValue|CallableValue|HandlerFrame|ContinuationValue|HostRequest',
    'load frozen image|invoke function|execute instruction|dispatch effect|resume continuation|run cleanup|request host operation|enforce runtime meter',
    'raw artifact execution|stale arena handle|ambient host access|continuation double use|cleanup divergence|resource-limit bypass',
    'bytecode verifier|supervisor|capability adapters|runtime diagnostics|conformance tests',
    'runtime outcome|execution trace|memory profile|host audit log|worker crash report',
    'arena allocation model|cycle reclamation policy|tail-call implementation|worker protocol|runtime determinism guarantees'),
  section(29, 'Diagnostics, Explanations, and Machine-Applicable Fixes',
    'the structured diagnostic model and phase-specific exhaustive adapters',
    'DiagnosticCode|DiagnosticClass|DiagnosticSite|DiagnosticLabel|ExplanationNode|MachineFix|RenderPlan|DiagnosticSet',
    'construct diagnostic|attach primary and related sites|build explanation graph|propose machine fix|deduplicate and sort|render terminal output|encode JSON response|compare golden diagnostic',
    'string-only error channel|unstable diagnostic ordering|lost semantic provenance|unsafe automatic fix|invariant reported as user error|unbounded diagnostic flood',
    'all compiler phases|language server|CLI adapters|test harness|documentation',
    'structured diagnostic|explanation graph|fix set|rendered output|golden fixture',
    'diagnostic code namespace|localization strategy|source excerpt ownership|deduplication policy|verbosity levels'),
  section(30, 'Compiler Service APIs and Tooling',
    'the long-lived compiler service and thin protocol clients',
    'CompilerService|LspSession|DocumentVersion|SemanticPosition|HoverResult|ReferenceSet|RenamePlan|InspectionRequest',
    'open document revision|create workspace snapshot|request hover|request completion|find definition|find references|construct rename|format source|inspect intermediate representation',
    'second semantic implementation|stale editor response|source write without consent|recovered fact used as release truth|position encoding mismatch|daemon and CLI divergence',
    'typed query engine|lossless source model|structured diagnostics|formatter|grand orchestration',
    'LSP response|workspace edit plan|documentation model|inspection bundle|service metrics',
    'daemon deployment|service protocol|partial-result streaming|workspace scaling|cancellation semantics'),
  section(31, 'Testing, Differential Oracles, Fuzzing, and Performance',
    'repository-wide test, fuzz, benchmark, and CI infrastructure',
    'TestCase|Oracle|PhaseFingerprint|DifferentialPair|FuzzCorpus|Benchmark|ResourceGate|ReproductionBundle',
    'run unit test|run compile-pass test|run compile-fail test|run differential oracle|fuzz hostile input|measure benchmark|compare deterministic builds|run self-host resource gate',
    'flaky nondeterministic test|oracle trusted outside its model|golden overfitting|performance noise|missing hostile boundary cases|manual-only continuous integration',
    'every compiler subsystem|CI workflows|bootstrap process|diagnostic goldens|profiling tools',
    'test report|minimized reproducer|performance baseline|fuzz corpus|reproduction script',
    'CI sharding|continuous fuzz budget|oracle authority|benchmark hardware normalization|release gating policy'),
  section(32, 'Self-Hosting, Bootstrap Convergence, Migration, and Release',
    'the bootstrap driver, self-host parity program, release engineering, verifier, and VM',
    'StageZero|StageOne|StageTwo|StageThree|SeedArtifact|ParityLedger|BootstrapManifest|ReleaseBundle',
    'compile stage one|verify stage one|compile stage two|verify stage two|compile stage three|compare stage artifacts|package release|reproduce seed',
    'premature self-host claim|hidden Rust semantic shortcut|bootstrap nondeterminism|seed compromise|parity coverage gap|self-compilation resource failure',
    'self-hosted compiler|standard library|bytecode verifier|VM and supervisor|release CI',
    'canonical seed artifact|stage artifacts|bootstrap manifest|release checksums|parity ledger',
    'seed trust policy|release signing|distribution contents|compatibility commitments|retirement of bootstrap probes'),
];

const pad = (n) => String(n).padStart(2, '0');
const snake = (value) => value.toLowerCase().replace(/[^a-z0-9]+/g, '_').replace(/^_+|_+$/g, '');
const sentence = (value) => value.charAt(0).toUpperCase() + value.slice(1);
const bullet = (value) => `- ${value}`;
const numbered = (n, value) => `${n}. ${value}`;

function generatedBlock(s) {
  const out = [];
  const begin = `<!-- BEGIN GENERATED EXPANSION ${pad(s.n)} -->`;
  const end = `<!-- END GENERATED EXPANSION ${pad(s.n)} -->`;
  out.push(begin, '', '### Expanded implementation contract', '');
  out.push(bullet(`Authoritative owner: ${s.owner}.`));
  out.push(bullet('All inputs are immutable and revision-qualified.'));
  out.push(bullet('All successful products publish only after validation.'));
  out.push(bullet('Recovery, cancellation, limits, corruption, and invariants remain distinct.'));
  out.push(bullet('Cold execution is the semantic reference; reuse changes performance only.'), '');

  out.push('#### Contracted data types', '');
  for (const concept of s.concepts) {
    out.push(`##### \`${concept}\``, '');
    out.push(bullet(`Role: represent ${sentence(concept.replace(/([a-z0-9])([A-Z])/g, '$1 $2').toLowerCase())}.`));
    out.push(bullet('Identity: typed stable key or owner-local typed arena identity.'));
    out.push(bullet('Ownership: the shortest-lived context capable of containing mutation.'));
    out.push(bullet('Revision: explicitly global, revision-qualified, package-local, body-local, or query-local.'));
    out.push(bullet('Validation: constructed, recovered, validated, and publishable states are distinguishable.'));
    out.push(bullet('Fingerprint: semantic equality excludes spans and allocation order unless requested.'));
    out.push(bullet('Persistence: canonical encoding with local-ID remapping, or explicit nonpersistence.'));
    out.push(bullet('Inspection: stable borrowed view without exposing private arena layout.'));
    out.push(bullet('Failure: stale generations and foreign identity spaces fail closed.'));
    out.push(bullet('Tests: stale key, round trip, deterministic order, validation, and lifetime.'), '');
  }

  out.push('#### Typed query surface', '');
  s.operations.forEach((operation, index) => {
    const query = snake(operation);
    const key = s.concepts[index % s.concepts.length];
    const product = s.products[index % s.products.length];
    out.push(`##### \`${query}\``, '');
    out.push(bullet(`Conceptual signature: \`${query}(snapshot: &DatabaseSnapshot, key: ${key}Key) -> Analysis<Value>\`.`));
    out.push(bullet(`Purpose: ${operation}.`));
    out.push(bullet(`Primary product: ${product}.`));
    out.push(bullet('Dependencies: every direct input and nested query is recorded automatically.'));
    out.push(bullet('Precondition: imported persistent data is decoded and validated before semantic use.'));
    out.push(bullet('Cancellation: polling occurs at bounded structural work boundaries.'));
    out.push(bullet('Budget: work units and retained bytes charge the request budget tree.'));
    out.push(bullet('Publication: the result remains staged until all local invariants pass.'));
    out.push(bullet('Recovery: release roots require completeness; tooling opts into recovery explicitly.'));
    out.push(bullet('Explanation: report hit, green validation, recomputation, recovery, limit, or cancellation.'));
    out.push(bullet('Tests: success, rejection, recovery, cancellation, limits, deterministic replay, and reuse.'), '');
  });

  out.push('#### Normal processing order', '');
  s.operations.forEach((operation, index) => out.push(numbered(index + 1, `Perform **${operation}** against the pinned revision.`)));
  out.push(numbered(s.operations.length + 1, 'Validate every produced node, range, edge, and referenced identity.'));
  out.push(numbered(s.operations.length + 2, 'Attach semantic and presentation fingerprints, provenance, diagnostics, and source mappings.'));
  out.push(numbered(s.operations.length + 3, 'Check cancellation and remaining budget immediately before publication.'));
  out.push(numbered(s.operations.length + 4, 'Publish atomically, or discard all staged success and return the classified failure.'), '');

  out.push('#### Ownership and retention', '');
  out.push(bullet(`Primary mutable owner: ${s.owner}.`));
  out.push(bullet('Database lifetime: immutable inputs, interners, revision records, validated memos, and eviction metadata.'));
  out.push(bullet('Request lifetime: cancellation, hierarchical budgets, demanded roots, and diagnostic staging.'));
  out.push(bullet('Package lifetime: package-wide indexes and immutable shared semantic state.'));
  out.push(bullet('Body lifetime: syntax, local resolution, inference variables, Core building, and lowering scratch.'));
  out.push(bullet('Query lifetime: dependency journal, explanation builder, and publication guard.'));
  out.push(bullet('Emission lifetime: canonical pools, remaps, relocations, and serialization scratch.'));
  out.push(bullet('Temporary arenas are never promoted merely because a later phase prefers another storage layout.'));
  out.push(bullet('Every retained allocation is attributable to an owner, revision, query family, and retention class.'), '');

  out.push('#### Hazard controls', '');
  for (const hazard of s.hazards) {
    out.push(`##### ${sentence(hazard)}`, '');
    out.push(bullet(`Detection: identify ${hazard} before publication.`));
    out.push(bullet('Containment: fail closed or recompute; never manufacture a successful semantic fact.'));
    out.push(bullet('Classification: preserve the exact source, recovery, limit, corruption, invariant, verifier, or runtime class.'));
    out.push(bullet('Authority: the failure path acquires no additional host capability.'));
    out.push(bullet('Explanation: record semantic owner, expected invariant, observed facts, and relevant source sites.'));
    out.push(bullet('Resource safety: bound recursion, allocation, graph growth, diagnostics, and output.'));
    out.push(bullet('Regression: retain a minimized deterministic reproducer.'));
    out.push(bullet('Fuzzing: include the boundary in hostile-input corpora when bytes are external.'));
    out.push(bullet('Migration: delete compatibility behavior whose only purpose is to conceal the hazard.'), '');
  }

  out.push('#### Semantic and structural invariants', '');
  [
    'Published identities belong to a compatible database and revision.',
    'Published graphs contain valid edges, ranges, owners, and discriminants.',
    'Persistent records contain no raw local arena identity without canonical remapping.',
    'Recovered values cannot enter release roots without complete recomputation.',
    'Evaluation order and trapping behavior are preserved.',
    'Ownership, borrowing, and cleanup obligations are preserved.',
    'Effects, handlers, resumptions, and cancellation behavior are preserved.',
    'Runtime capabilities remain explicit and independently enforced.',
    'Ordinary source names grant no compiler, primitive, verifier, or runtime privilege.',
    'Every published collection has deterministic iteration and serialization order.',
  ].forEach((item) => out.push(bullet(item)));
  s.hazards.forEach((hazard) => out.push(bullet(`Invariant: ${hazard} cannot be hidden by a fallback path.`)));
  out.push('');

  out.push('#### Cycles and fixed points', '');
  [
    'Every recursive query family declares an acyclic, SCC, tabled/coinductive, or fixed-point policy.',
    'Illegal cycles produce a typed diagnostic with the complete semantic key chain.',
    'SCC membership and worklist order are deterministic.',
    'Fixed points define bottom, transfer, join, widening, convergence, and overflow.',
    'Tabled solvers distinguish provisional assumptions from completed answers.',
    'Resource overflow remains distinct from semantic rejection.',
  ].forEach((item) => out.push(bullet(item)));
  const policies = ['acyclic', 'SCC-grouped', 'bounded fixed point', 'tabled or coinductive'];
  s.concepts.slice(0, 6).forEach((concept, index) => out.push(bullet(`Initial review policy for \`${concept}\`: **${policies[index % policies.length]}**.`)));
  out.push('');

  out.push('#### Incremental dependency contract', '');
  [
    'Record every input-leaf read.',
    'Record every nested typed-query demand.',
    'Separate semantic, source-map, diagnostic, target, optimizer, and presentation fingerprints.',
    'Preserve stable identity across revisions before comparing values.',
    'Validate all observed dependencies before reusing a memo.',
    'Recompute red nodes only.',
    'Permit downstream green reuse when recomputation produces an equal semantic fingerprint.',
    'Never use timestamps or host changed-file hints as semantic evidence.',
    'Expose the first changed dependency through `why_recompiled`.',
    'Expose unexpectedly broad fanout as a compiler performance defect.',
  ].forEach((item) => out.push(bullet(item)));
  s.integrations.forEach((integration) => out.push(bullet(`The projection imported from **${integration}** is named, versioned, and tested.`)));
  out.push('');

  out.push('#### Cache and persistence contract', '');
  [
    'A cold build may ignore every cache entry.',
    'Every key includes every semantic influence relevant to the product.',
    'Every entry carries schema, language, compiler-build, and producer identities.',
    'Every entry carries a checksum before decode.',
    'Every decoded graph is structurally validated before memo candidacy.',
    'Recovered, cancelled, limited, corrupt, and invariant-failed values are never persisted as success.',
    'Corrupt records are quarantined or ignored and then recomputed.',
    'Eviction changes latency and retained memory only.',
    'Warm and cold builds produce identical diagnostics, manifests, interfaces, and artifacts.',
  ].forEach((item) => out.push(bullet(item)));
  s.products.forEach((product) => {
    out.push(bullet(`Persistence decision required for **${product}**.`));
    out.push(bullet(`Independent validator required before reusing **${product}**.`));
    out.push(bullet(`Canonical serializer required if **${product}** crosses a process boundary.`));
  });
  out.push('');

  out.push('#### Diagnostic and explanation contract', '');
  [
    'Diagnostics use stable codes and typed location spaces.',
    'Primary, related, owner, and generated locations remain distinct.',
    'Expected and observed facts are structured rather than embedded only in prose.',
    'Explanation graphs have deterministic node and edge order.',
    'User errors remain distinct from compiler invariant failures.',
    'Resource limits remain distinct from cancellation.',
    'Corruption remains distinct from source rejection.',
    'Machine-applicable fixes target the exact producing revision.',
    'Diagnostic count, source excerpt size, and explanation depth are bounded.',
  ].forEach((item) => out.push(bullet(item)));
  s.hazards.forEach((hazard) => out.push(bullet(`Stable explanation path required for **${hazard}**.`)));
  out.push('');

  out.push('#### Cancellation and resource limits', '');
  [
    'Cancellation tokens are request scoped and revision qualified.',
    'Cancellation checks occur at bounded parser, solver, graph, optimizer, and serializer work intervals.',
    'Budgets form a hierarchical tree and child work cannot exceed parent allowance.',
    'Recursion is bounded or converted into an explicit worklist.',
    'Input-driven collection growth is checked before allocation.',
    'Diagnostic count and explanation depth are bounded.',
    'Persistent and executable output sizes are bounded.',
    'Cancellation publishes no partial successful value.',
    'A completed child query survives parent cancellation only after its own validation and publication.',
  ].forEach((item) => out.push(bullet(item)));
  s.hazards.slice(0, 4).forEach((hazard) => out.push(bullet(`Concrete structural limit required for the resource dimension exposed by **${hazard}**.`)));
  out.push('');

  out.push('#### Determinism, security, and trust', '');
  [
    'Wall-clock time never enters semantic output.',
    'Random seeds never enter semantic output.',
    'Memory addresses never enter semantic output.',
    'Hash-table iteration order never enters semantic output.',
    'Absolute checkout paths never enter semantic fingerprints or artifacts.',
    'Tie breaking and worklist order are specified.',
    'Canonical pools freeze and remap before serialization.',
    'External lengths are checked before allocation.',
    'Unknown critical features fail closed.',
    'Compiler checking, bytecode verification, runtime supervision, reproducibility, and formal proof remain distinct claims.',
  ].forEach((item) => out.push(bullet(item)));
  s.hazards.forEach((hazard) => out.push(bullet(`Adversarial containment test required for **${hazard}**.`)));
  out.push('');

  out.push('#### Integration contracts', '');
  for (const integration of s.integrations) {
    out.push(`##### ${sentence(integration)}`, '');
    out.push(bullet('Define the authoritative producer and consumer.'));
    out.push(bullet('Define every identity and product crossing the boundary.'));
    out.push(bullet('Define borrowed, moved, copied, and persisted ownership.'));
    out.push(bullet('Define revision compatibility and observed fingerprint projections.'));
    out.push(bullet('Define cancellation, corruption, limit, and invariant propagation.'));
    out.push(bullet('Define which side validates imported data.'));
    out.push(bullet('Define canonical order and deterministic tie breaking.'));
    out.push(bullet('Name the current implementation path that migration removes.'));
    out.push(bullet('Provide one production producer-consumer parity test.'), '');
  }

  out.push('#### Product contracts', '');
  for (const product of s.products) {
    out.push(`##### ${sentence(product)}`, '');
    out.push(bullet(`Authoritative producer: ${s.owner}.`));
    out.push(bullet('Recovered and complete forms are distinguishable.'));
    out.push(bullet('The typed product key and schema generation are explicit.'));
    out.push(bullet('Semantic and presentation fingerprints are separate.'));
    out.push(bullet('Serialization is canonical or explicitly unsupported.'));
    out.push(bullet('Validation is independent of producer convenience checks.'));
    out.push(bullet('Source mapping is retained only when it is part of the product contract.'));
    out.push(bullet('Persistence is optional and never authoritative.'));
    out.push(bullet('Cold and warm production are deterministic.'));
    out.push(bullet('Tests include round trip, corruption, stale schema, and reproducibility.'), '');
  }

  out.push('#### Test plan', '');
  [
    'Unit tests cover every public constructor and validator.',
    'Property tests cover canonicalization, remapping, and stable fingerprints.',
    'Incremental tests cover equal and unequal dependency projections.',
    'Cancellation tests interrupt every publication boundary.',
    'Resource tests cover every unbounded-looking loop, recursion, and collection.',
    'Corruption tests cover every persisted input family.',
    'Determinism tests vary insertion order, request order, and cache warmth.',
    'Cold and warm tests compare every externally visible product.',
    'Differential tests compare Rust bootstrap and self-host products where an oracle exists.',
    'Performance tests report elapsed time, retained bytes, executed queries, and invalidation fanout.',
  ].forEach((item) => out.push(bullet(item)));
  s.operations.forEach((operation) => out.push(bullet(`Operation fixture: **${operation}**.`)));
  s.hazards.forEach((hazard) => out.push(bullet(`Adversarial fixture: **${hazard}**.`)));
  s.products.forEach((product) => out.push(bullet(`Product fixture: **${product}**.`)));
  out.push('');

  out.push('#### Migration plan', '');
  s.integrations.forEach((integration, index) => out.push(numbered(index + 1, `Inventory current **${integration}** responsibilities and tests.`)));
  let step = s.integrations.length + 1;
  out.push(numbered(step++, 'Locate duplicate semantic representations, raw identities, ambient effects, custom serializers, and hidden caches.'));
  out.push(numbered(step++, 'Introduce typed immutable boundary products and revision-qualified keys.'));
  out.push(numbered(step++, 'Move one real producer and one real consumer behind differential or parity tests.'));
  out.push(numbered(step++, 'Add cancellation, resource, corruption, and determinism coverage.'));
  out.push(numbered(step++, 'Measure memory, invalidation fanout, deterministic output, and build time.'));
  out.push(numbered(step++, 'Delete the superseded authoritative path rather than preserving permanent dual semantics.'));
  out.push(numbered(step++, 'Update parity ledgers, remaining-work records, and architecture documentation.'), '');

  out.push('#### Open design decisions', '');
  for (const decision of s.decisions) {
    out.push(bullet(`Decision: **${decision}**.`));
    out.push(bullet('Evaluate semantic simplicity and auditability.'));
    out.push(bullet('Evaluate safe-Glorious implementability.'));
    out.push(bullet('Evaluate memory cost and incremental precision.'));
    out.push(bullet('Evaluate deterministic behavior and migration evidence.'));
  }
  out.push('');

  out.push('#### Rejected alternatives', '');
  [
    'Ambient host discovery inside semantic phases.',
    'Cache records treated as semantic truth.',
    'Permanent parallel implementations of the same fact.',
    'Allocation order or memory address used as persistent identity.',
    'A universal dynamically typed query dispatcher.',
    'Partial publication after cancellation or resource exhaustion.',
    'Optimization justified only by tests without a stated semantic invariant.',
  ].forEach((item) => out.push(bullet(`Reject: ${item}`)));
  s.hazards.forEach((hazard) => out.push(bullet(`Reject designs that silently tolerate **${hazard}**.`)));
  out.push('');

  out.push('#### Acceptance checklist', '');
  [
    'Inputs and outputs are typed and revision compatible.',
    'Authority, mutable owner, and retention lifetime are documented.',
    'Semantic code requires no ambient host capability.',
    'Publication is atomic and follows validation.',
    'Recovered values cannot enter release roots unnoticed.',
    'Dependencies are recorded automatically and explainable.',
    'Invalidation is narrow and auditable.',
    'Cold and warm products are identical.',
    'Corrupt persisted data fails closed or recomputes.',
    'Cancellation and limits release temporary state.',
    'Diagnostics retain source and semantic provenance.',
    'Every published collection has deterministic order.',
    'Focused, adversarial, differential, and migration tests exist.',
    'The production entry point uses the new contract.',
    'The superseded authoritative path is removed.',
  ].forEach((item) => out.push(bullet(`[ ] ${item}`)));
  out.push('', end);
  return out.join('\n');
}

let source = fs.readFileSync(TARGET, 'utf8').replace(/\r\n/g, '\n');
source = source.replace(/\n?<!-- BEGIN GENERATED EXPANSION \d{2} -->[\s\S]*?<!-- END GENERATED EXPANSION \d{2} -->\n?/g, '\n');
source = source.replace(/^Status: breadth-first snowflake design\./m,
  'Status: expanded breadth-first snowflake implementation workbook.');

for (let index = sections.length - 1; index >= 0; index -= 1) {
  const s = sections[index];
  const escaped = s.title.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const heading = new RegExp(`^## ${pad(s.n)}\\. ${escaped}$`, 'm');
  const match = heading.exec(source);
  if (!match) throw new Error(`missing section heading ${pad(s.n)}: ${s.title}`);
  const nextHeading = index + 1 < sections.length
    ? new RegExp(`^## ${pad(sections[index + 1].n)}\\. `, 'm')
    : /^# Using the Compendium$/m;
  const tail = source.slice(match.index + match[0].length);
  const nextMatch = nextHeading.exec(tail);
  const insertAt = nextMatch ? match.index + match[0].length + nextMatch.index : source.length;
  const prefix = source.slice(0, insertAt).replace(/\s+$/, '');
  const suffix = source.slice(insertAt).replace(/^\s+/, '');
  source = `${prefix}\n\n${generatedBlock(s)}\n\n${suffix}`;
}

source = source.replace(/\n{4,}/g, '\n\n\n').trimEnd() + '\n';
const lineCount = source.split('\n').length - 1;
const sectionCount = (source.match(/^## \d{2}\. /gm) ?? []).length;
const volumeCount = (source.match(/^# Volume /gm) ?? []).length;
const blockCount = (source.match(/<!-- BEGIN GENERATED EXPANSION \d{2} -->/g) ?? []).length;
const endBlockCount = (source.match(/<!-- END GENERATED EXPANSION \d{2} -->/g) ?? []).length;

if (lineCount < 10000) throw new Error(`line count ${lineCount} is below 10000`);
if (sectionCount !== 32) throw new Error(`expected 32 numbered sections, found ${sectionCount}`);
if (volumeCount !== 8) throw new Error(`expected 8 volumes, found ${volumeCount}`);
if (blockCount !== 32 || endBlockCount !== 32) throw new Error(`generated block mismatch ${blockCount}/${endBlockCount}`);
if (!source.includes('## 32. Self-Hosting, Bootstrap Convergence, Migration, and Release')) throw new Error('missing final section');

fs.writeFileSync(TARGET, source, 'utf8');
console.log(JSON.stringify({ target: TARGET, lineCount, sectionCount, volumeCount, blockCount, bytes: Buffer.byteLength(source) }));
