import GloriousLanguage.Contracts

/-! Target obligations are not an implementation of a compiler. In
particular, source labels may use mathematical delimiters in the semantics,
but an admitted target must erase them through a checked direct-control map.
Shared backing, mandatory tail transfer and loader admission are independent
of ordinary observational equivalence. -/
namespace Glorious.Language.ABI

open Kernel Execution Memory

structure ConcreteType where
  identity : Identity
  type : Term
  layout : Layout
  principal : Principal
  drop : Option DeclId
  deriving Repr, Inhabited

structure Descriptor where
  generation : Nat
  target : Identity
  triple : String
  pointerBits : Nat
  endian : Endianness
  layoutIdentity : Identity
  callableConvention : Identity
  effectConvention : Identity
  manifest : Identity
  concrete : List ConcreteType
  deriving Repr, Inhabited

/-- The selected target owns every ABI identity field. A descriptor cannot
choose an unrelated layout generation while retaining the target's identity. -/
structure Descriptor.Matches (program : Kernel.Program) (descriptor : Descriptor) : Prop where
  generation : descriptor.generation = program.declarations.input.target.generation
  target : descriptor.target = program.declarations.input.target.identity
  triple : descriptor.triple = program.declarations.input.target.triple
  pointerBits : descriptor.pointerBits = program.declarations.input.target.pointerBits
  endian : descriptor.endian = program.declarations.input.target.endian
  layoutIdentity : descriptor.layoutIdentity = program.declarations.input.target.layoutIdentity
  callableConvention : descriptor.callableConvention = program.declarations.input.target.callableConvention
  effectConvention : descriptor.effectConvention = program.declarations.input.target.effectConvention
  manifest : descriptor.manifest = program.declarations.input.manifest.identity

/-- A mathematical layout is not yet a concrete ABI admission. Its size must
respect the advertised object limit, and both public layout-query components
must be representable as target usize values. -/
structure ConcreteType.Valid (program : Kernel.Program) (concrete : ConcreteType) : Prop where
  closed : Closed concrete.type
  layout : LayoutOf program.declarations ⟨[],[],0,default,false,{}⟩ concrete.type concrete.layout
  sizeLimit : concrete.layout.size ≤ program.declarations.input.target.maximumObjectBytes
  sizeRange : IntegerRange program.declarations.input.target false .pointer concrete.layout.size
  alignmentRange : IntegerRange program.declarations.input.target false .pointer concrete.layout.alignment
  principal : PrincipalOf program.declarations concrete.type concrete.principal
  drop : DropHook program.declarations concrete.type concrete.drop

structure Descriptor.Valid (program : Kernel.Program) (descriptor : Descriptor) : Prop where
  targetContract : descriptor.Matches program
  identities : (descriptor.concrete.map (·.identity)).Nodup
  concrete : ∀ concrete ∈ descriptor.concrete, concrete.Valid program

def Compatible (left right : Descriptor) : Prop :=
  left.generation = right.generation ∧ left.target = right.target ∧ left.triple = right.triple ∧
  left.pointerBits = right.pointerBits ∧ left.endian = right.endian ∧ left.layoutIdentity = right.layoutIdentity ∧
  left.callableConvention = right.callableConvention ∧ left.effectConvention = right.effectConvention ∧ left.manifest = right.manifest ∧
  ∀ a ∈ left.concrete, ∀ b ∈ right.concrete, a.identity = b.identity →
    a.type = b.type ∧ a.layout = b.layout ∧ a.principal = b.principal ∧ a.drop = b.drop

structure Buffer where
  identity : Identity
  address : Nat
  generation : Nat
  alignment : Nat
  domain : Identity
  bytes : List (Option Nat)
  live : Bool
  deriving Repr, Inhabited

structure Backing where
  identity : Identity
  buffers : Table Buffer
  deriving Repr, Inhabited

structure Injection where
  storage : Identity → Identity
  offset : Address → Nat
  owner : Identity → Identity
  loan : Identity → Identity

def Represents (program : Kernel.Program) (runtime : RuntimeAddresses) (world : World)
    (backing : Backing) (injection : Injection) : Prop :=
  backing.buffers.Unique ∧
  (∀ a b left right, world.roots.get a = some left → world.roots.get b = some right →
    left.live = true → right.live = true → injection.storage a = injection.storage b → a = b) ∧
  (∀ a b, a < world.nextOwner → b < world.nextOwner → injection.owner a = injection.owner b → a = b) ∧
  (∀ id root, world.roots.get id = some root → root.live = true → ∃ buffer bytes,
    backing.buffers.get (injection.storage id) = some buffer ∧ buffer.live = true ∧
    buffer.identity = injection.storage id ∧ buffer.generation = root.generation ∧ buffer.address = root.base ∧
    buffer.alignment = root.layout.alignment ∧ buffer.bytes = bytes ∧ ObjectBytes program.declarations world runtime id bytes) ∧
  (∀ address value physical, world.Resident address value → PhysicalAddress program.declarations world address value.type physical →
    ∃ root, world.root address = some root ∧ physical = root.base + injection.offset address)

structure Engine (Event Result : Type) where
  semantics : TransitionSystem Event Result
  descriptor : Descriptor
  backing : semantics.State → Backing
  home : semantics.State → Address → Option (Identity × Nat)
  administrativeControl : semantics.State → Nat
  activationRetained : semantics.State → Identity → Prop
  directTransfer : semantics.State → Identity → semantics.State → Prop
  sourceState : semantics.State → State → Prop

variable {Event Result : Type}

def SharedHome (vm : Engine Event Result) (native : Engine Event Result)
    (vmState : vm.semantics.State) (nativeState : native.semantics.State) (address : Address) : Prop :=
  (vm.backing vmState).identity = (native.backing nativeState).identity ∧
  vm.backing vmState = native.backing nativeState ∧
  vm.home vmState address = native.home nativeState address ∧ (vm.home vmState address).isSome = true

def SharedABI (program : Kernel.Program) (runtime : RuntimeAddresses)
    (vm native : Engine Event Result) : Prop :=
  vm.descriptor.Valid program ∧ native.descriptor.Valid program ∧ Compatible vm.descriptor native.descriptor ∧
  ∀ source vmState nativeState, vm.sourceState vmState source → native.sourceState nativeState source →
    ∃ injection,
      Represents program runtime source.world (vm.backing vmState) injection ∧
      Represents program runtime source.world (native.backing nativeState) injection ∧
      ∀ address value, source.world.Resident address value →
        Addressable program.declarations ⟨[],[],0,default,false,{}⟩ value.type → SharedHome vm native vmState nativeState address

/-- A crossing changes which engine executes, not the backing allocation or
the concrete identity of an addressable argument. Ordinary source moves are
accounted for separately by the common ownership transition. -/
def ZeroMarshalling (sourceSide to : Engine Event Result)
    (before : sourceSide.semantics.State) (after : to.semantics.State) (arguments : List InvocationInput) : Prop :=
  sourceSide.backing before = to.backing after ∧
  ∀ input ∈ arguments, sourceSide.home before input.storage = to.home after input.storage

structure TailSite where
  function : DeclId
  syntaxNode : Identity
  sourceActivation : Identity
  destination : Identity
  deriving Repr, Inhabited

structure TailEvidence (engine : Engine Event Result) where
  site : TailSite
  entry : engine.semantics.State → Prop
  landed : engine.semantics.State → Prop
  bound : Nat
  transfer : ∀ before, entry before → ∃ trace after,
    engine.semantics.Steps before trace after ∧ landed after ∧
    ¬ engine.activationRetained after site.sourceActivation ∧ engine.administrativeControl after ≤ bound
  repeated : ∀ states : Nat → engine.semantics.State,
    (∀ n, entry (states n) ∧ landed (states (n+1))) →
    ∀ n, engine.administrativeControl (states n) ≤ bound

structure LabelSite where
  function : DeclId
  syntaxNode : Identity
  brand : Identity
  destination : Identity
  deriving Repr, Inhabited

structure LabelFusion (engine : Engine Event Result) where
  sites : List LabelSite
  target : engine.semantics.State → LabelSite → Prop
  noRuntimeAddress : ∀ state site, target state site →
    ∀ address value source, engine.sourceState state source → source.world.Resident address value → value.head = .label site.brand →
      engine.home state address = none
  direct : ∀ before site, target before site → ∃ after, engine.directTransfer before site.destination after
  unique : ∀ state a b, target state a → target state b → a.syntaxNode = b.syntaxNode → a.destination = b.destination

inductive WireScalar where
  | integer (signed : Bool) (width : Width) (magnitude : List Nat)
  | floating (width : FloatWidth) (bits : List Nat)
  | character (scalar : Nat)
  deriving Repr, Inhabited

structure Artifact where
  format : Identity
  descriptor : Descriptor
  imports : List DeclId
  constants : List WireScalar
  relocations : List (Identity × DeclId)
  body : List Nat
  requiredFeatures : List Identity
  deriving Repr, Inhabited

structure LoaderContract where
  format : Identity
  supportedFeatures : List Identity
  decode : List Nat → Except Failure Artifact
  canonical : Artifact → List Nat
  roundtrip : ∀ artifact, artifact.format = format → decode (canonical artifact) = .ok artifact

/-- Decoding alone never admits an artifact. The actual loader boundary
consumes the target-matched descriptor and its concrete representation bounds
before any engine can use the artifact's identities or object layouts. -/
structure AdmittedArtifact (program : Kernel.Program) (loader : LoaderContract)
    (bytes : List Nat) (artifact : Artifact) : Prop where
  decoded : loader.decode bytes = .ok artifact
  format : artifact.format = loader.format
  descriptor : artifact.descriptor.Valid program
  features : ∀ feature ∈ artifact.requiredFeatures, feature ∈ loader.supportedFeatures
  imports : ∀ id ∈ artifact.imports, ∃ binding ∈ program.declarations.input.manifest.bindings, binding.declaration = id
  relocations : (artifact.relocations.map Prod.fst).Nodup
  constants : ∀ scalar ∈ artifact.constants, match scalar with
    | .integer _ width bytes => bytes.length = width.bits program.declarations.input.target / 8 ∧ ∀ byte ∈ bytes, byte < 256
    | .floating width bytes => bytes.length = (if width = .single then 4 else 8) ∧ ∀ byte ∈ bytes, byte < 256
    | .character value => Source.UnicodeScalar value

theorem incompatible_width_not_linkable {left right : Descriptor} (different : left.pointerBits ≠ right.pointerBits) :
    ¬ Compatible left right := by
  intro compatible
  exact different compatible.2.2.2.1

end Glorious.Language.ABI
