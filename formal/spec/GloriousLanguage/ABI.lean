import GloriousLanguage.Contracts

/-! Target obligations are not an implementation of a compiler. In
particular, source labels may use mathematical delimiters in the semantics,
but an admitted target must erase them through a checked direct-control map.
Shared backing, mandatory tail transfer and loader admission are independent
of ordinary observational equivalence. -/
universe u

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

/-- The source operational system is the actual execution relation. Each engine
relates its states to these source states; invocation-specific initial, final,
and invalid predicates are supplied by the actual source semantics consumer. -/
def SourceSemantics (program : Kernel.Program) (host : Foreign.Model) :
    TransitionSystem Execution.Event Unit where
  State := State
  initial _ := False
  step before event after := Execution.Step program host before event after
  final _ _ := False
  invalid _ := False

/-- A represented engine is tied to the source machine by a weak two-way step
relation. Steps may stutter or expand into finite paths; well-founded zero matches
prevent infinite mismatched stuttering while permitting genuine silent divergence.
Initial-state coverage and invocation terminal correspondence are stated at the
compiler boundary, where the concrete invocation is known. -/
structure Engine (Event Result : Type) : Type (u + 1) where
  program : Kernel.Program
  host : Foreign.Model
  semantics : TransitionSystem Event Result
  /-- The source event observed by one engine step. Internal machine events
  without an observable counterpart map to none. -/
  observe : Execution.Event → Option Event
  descriptor : Descriptor
  backing : semantics.State → Backing
  home : semantics.State → Address → Option (Identity × Nat)
  administrativeControl : semantics.State → Nat
  directTransfer : semantics.State → Identity → semantics.State → Prop
  sourceState : semantics.State → State → Prop
  Rank : Type u
  rankDecrease : Rank → Rank → Prop
  rankWellFounded : WellFounded rankDecrease
  /-- A variant for pairs related by `sourceState`; every empty transition match
  must strictly decrease it in the side that stutters. -/
  stutterRank : semantics.State → State → Rank
  /-- A source step either has a genuinely nonempty engine path with exactly its
  observed event, or stutters at the same engine state with a tied rank decrease. -/
  realizes : ∀ before event after, Execution.Step program host before event after →
    ∀ implementing, sourceState implementing before →
      (∃ target, semantics.PositiveSteps implementing (event.bind observe).toList target ∧
        sourceState target after) ∨
      (event.bind observe = none ∧ sourceState implementing after ∧
        rankDecrease (stutterRank implementing after) (stutterRank implementing before))
  /-- Every target transition is reflected by a finite nonempty source path with
  the same mapped observations, or by zero source steps with a tied rank decrease. -/
  reflects : ∀ implementing event target, semantics.step implementing event target →
    ∀ source, sourceState implementing source →
      (∃ after trace, (SourceSemantics program host).PositiveSteps source trace after ∧
        trace.filterMap observe = event.toList ∧ sourceState target after) ∨
      (event = none ∧ sourceState target source ∧
        rankDecrease (stutterRank target source) (stutterRank implementing source))

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

/-- The declaration a running context executes: the innermost resource contract
installed at its entry. Entry installs the running function's contract first and
proper-tail entry appends the caller's retained contracts, so the head of the
table is always the currently executing declaration. -/
def ExecutingDeclaration (context : Execution.Context) : Option DeclId :=
  context.resourceContracts.head?.map (fun entry => entry.declaration)

/-- A proper-tail site of a program: the declaring function and the syntactic
`tail` node itself. The activation a transfer retires is an execution fact, so
`TailSite.Entry` yields it from the source state instead of fixing it
statically. -/
structure TailSite where
  function : DeclId
  node : Code
  deriving Repr, Inhabited

/-- The source machine is at a real tail site: the next task is this exact
`tail` node, evaluated by the site's declaration in this activation. -/
def TailSite.Entry (state : Execution.State) (site : TailSite) (activation : Identity) : Prop :=
  ∃ context call, state.task = .run context (.tail call) ∧ site.node = .tail call ∧
    context.activation = activation ∧ ExecutingDeclaration context = some site.function

/-- The source machine landed a proper-tail transfer: `state` is the actual
successor of the machine's own step that retired `activation`. The transition
relation is the only producer. -/
def TailSite.Landed (program : Kernel.Program) (state : Execution.State) (activation : Identity) : Prop :=
  ∃ before destination, Execution.LocalStep program before (some (.tail activation destination)) state

/-- A label site of a program: the declaring function, the lexical brand that
must erase, and the enclosing activation region the direct leave returns to. -/
structure LabelSite where
  function : DeclId
  brand : Identity
  destination : Identity
  deriving Repr, Inhabited

/-- The source machine is leaving directly to this destination along a route to
the runtime image of the site's lexical brand. The runtime brand is read from
the actual instantiation of the label frame's context, so the site's lexical
brand is tied to the resident value that carries it. -/
def LabelSite.Leaves (state : Execution.State) (site : LabelSite) (destination : Identity) : Prop :=
  ∃ context runtime argument inner outerContext region type outer,
    state.task = .leave context runtime argument ∧
    LabelRoute state.frames runtime inner outerContext region type outer ∧
    outerContext.instantiation.brands.get site.brand = some (.label runtime) ∧
    outerContext.activation = destination

/-- Every engine state implementing a source state at the site performs the real
transfer. Entry and landed are the source machine's predicates, not predicates an
implementation may falsify; the trace is the engine's own, and administrative
control must not grow across the transfer, so iteration count cannot buy live
call storage. The `covered` field rejects an engine whose source relation is
empty, which is how the previous bare existential was satisfied.

Source facts come from the engine's own `program`; the compiler contract pins
that program to the artifact's source and pins the evidence list to the actual
site inventory. -/
structure TailEvidence (engine : Engine Event Result) where
  site : TailSite
  /-- Every actual entry into the site is implemented by some engine state. -/
  covered : ∀ source activation, site.Entry source activation →
    ∃ implementing, engine.sourceState implementing source
  /-- The request, callable selection and retirement are distinct machine
  states. The target must realize their composition within entry live control;
  requiring retirement directly from the pending syntax would be vacuous. -/
  transfer : ∀ implementing source context call declaration inputs entering activation destination landed,
    engine.sourceState implementing source → site.Entry source activation →
    source.task = .run context (.tail call) →
    Execution.LocalStep engine.program
      { source with task := .apply context (context.invocation call) true }
      (some (.call declaration inputs)) entering →
    Execution.LocalStep engine.program entering (some (.tail activation destination)) landed →
    ∃ trace target, engine.semantics.Steps implementing trace target ∧
      engine.sourceState target landed ∧
      engine.administrativeControl target ≤ engine.administrativeControl implementing

/-- The label clause: the proof-only brands of the program's actual label sites
obtain no target home, and every actual direct leave is realized by the engine's
own direct transfer to the destination the source route selected. -/
structure LabelFusion (engine : Engine Event Result) where
  sites : List LabelSite
  noRuntimeAddress : ∀ implementing source site,
    site ∈ sites → engine.sourceState implementing source →
    ∀ address value, source.world.Resident address value → value.head = .label site.brand →
      engine.home implementing address = none
  direct : ∀ implementing source site destination after,
    site ∈ sites → engine.sourceState implementing source → site.Leaves source destination →
    Execution.Step engine.program engine.host source none after →
    ∃ target, engine.directTransfer implementing destination target

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
