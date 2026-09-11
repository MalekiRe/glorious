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

def Descriptor.Valid (program : Kernel.Program) (descriptor : Descriptor) : Prop :=
  descriptor.generation = program.declarations.input.target.generation ∧
  descriptor.target = program.declarations.input.target.identity ∧ descriptor.triple = program.declarations.input.target.triple ∧
  descriptor.pointerBits = program.declarations.input.target.pointerBits ∧ descriptor.endian = program.declarations.input.target.endian ∧
  descriptor.callableConvention = program.declarations.input.target.callableConvention ∧
  descriptor.effectConvention = program.declarations.input.target.effectConvention ∧
  descriptor.manifest = program.declarations.input.manifest.identity ∧
  (descriptor.concrete.map (·.identity)).Nodup ∧
  (∀ concrete ∈ descriptor.concrete,
    Closed concrete.type ∧ LayoutOf program.declarations ⟨[],[],0,default,false⟩ concrete.type concrete.layout ∧
    PrincipalOf program.declarations concrete.type concrete.principal ∧ DropHook program.declarations concrete.type concrete.drop)

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
      ∀ address value, source.world.Resident address value → SharedHome vm native vmState nativeState address

/-- A crossing changes which engine executes, not the backing allocation or
the concrete identity of an addressable argument. Ordinary source moves are
accounted for separately by the common ownership transition. -/
def ZeroMarshalling (from to : Engine Event Result)
    (before : from.semantics.State) (after : to.semantics.State) (arguments : List InvocationInput) : Prop :=
  from.backing before = to.backing after ∧
  ∀ input ∈ arguments, from.home before input.storage = to.home after input.storage

structure TailSite where
  function : DeclId
  syntax : Identity
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
  syntax : Identity
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
  unique : ∀ state a b, target state a → target state b → a.syntax = b.syntax → a.destination = b.destination

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

def AdmittedArtifact (program : Kernel.Program) (loader : LoaderContract) (bytes : List Nat) (artifact : Artifact) : Prop :=
  loader.decode bytes = .ok artifact ∧ artifact.format = loader.format ∧ artifact.descriptor.Valid program ∧
  (∀ feature ∈ artifact.requiredFeatures, feature ∈ loader.supportedFeatures) ∧
  (∀ id ∈ artifact.imports, ∃ binding ∈ program.declarations.input.manifest.bindings, binding.declaration = id) ∧
  (artifact.relocations.map Prod.fst).Nodup ∧
  (∀ scalar ∈ artifact.constants, match scalar with
    | .integer _ width bytes => bytes.length = width.bits program.declarations.input.target / 8 ∧ ∀ byte ∈ bytes, byte < 256
    | .floating width bytes => bytes.length = (if width = .single then 4 else 8) ∧ ∀ byte ∈ bytes, byte < 256
    | .character value => Source.UnicodeScalar value)

theorem incompatible_width_not_linkable {left right : Descriptor} (different : left.pointerBits ≠ right.pointerBits) :
    ¬ Compatible left right := by
  intro compatible
  exact different compatible.2.2.2.1

end Glorious.Language.ABI
