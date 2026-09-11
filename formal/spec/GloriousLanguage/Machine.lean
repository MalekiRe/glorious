import GloriousLanguage.Instantiation

/-! Unbounded small-step execution. Control holds addresses into `World`,
never hidden copies of owners. Effects and machine leaves extend these tasks
in their respective modules; the final specification takes their union. -/
namespace Glorious.Language.Execution

open Kernel

structure Context where
  environment : Environment
  module : ModuleId
  activation : Identity
  scope : Identity
  region : Identity
  instantiation : ScopeInstantiation := {}
  unsafeAllowed : Bool := false
  deriving Repr, Inhabited

def Context.static (context : Context) : Language.Context :=
  ⟨[],[],0,context.module,context.unsafeAllowed⟩

def Context.bind (context : Context) (localSlot : Local) (address : Address) (authority : Authority := .owner) : Context :=
  { context with environment := ⟨localSlot.id,address,authority⟩ :: context.environment.filter (fun entry => entry.localSlot != localSlot.id) }

def Context.bindRegion (context : Context) (lexical runtime : Identity) : Context :=
  { context with instantiation := { context.instantiation with regions := context.instantiation.regions.set lexical runtime } }

def Context.bindBrand (context : Context) (lexical : Identity) (runtime : RuntimeBrand) : Context :=
  { context with instantiation := { context.instantiation with brands := context.instantiation.brands.set lexical runtime } }

def Context.term (context : Context) := context.instantiation.term

def Context.local (context : Context) (localSlot : Local) := localSlot.mapTerms context.term

def Context.invocation (context : Context) (call : Invocation) : Invocation :=
  { call with signature := call.signature.close context.instantiation }

structure InstalledHandler where
  identity : Identity
  syntaxNode : Handler
  environment : Context
  computation : Context
  outer : Context
  deriving Repr, Inhabited

inductive Task where
  | run (context : Context) (code : Code)
  | atom (context : Context) (destination : Address) (atom : Atom) (next : Code)
  | yield (context : Context) (value : Address)
  | apply (context : Context) (invocation : Invocation) (tail : Bool)
  | enter (context : Context) (function : Function) (inputs : List InvocationInput) (tail : Bool)
  | destroy (context : Context) (address : Address) (authority : Authority) (next : Task)
  | destroyFields (context : Context) (address : Address) (authority : Authority) (fields : List Nat) (next : Task)
  | finishShell (address : Address) (next : Task)
  | retire (root : Identity) (next : Task)
  | cleanup (context : Context) (roots : List Identity) (next : Task)
  | closeRegion (region : Identity) (next : Task)
  | closeLoan (loan : Identity) (next : Task)
  | transfer (source : Address) (authority : Authority) (destination : Address) (next : Task)
  | pattern (context : Context) (actions : List PatternAction) (body : Code)
  | perform (context : Context) (operation : DeclId) (arguments : List Term) (payload : List Address)
  | resume (context : Context) (continuation : Identity) (argument : Address) (tail : Bool)
  | cancel (context : Context) (continuation : Identity) (next : Task)
  | finishClause (handler : InstalledHandler) (ownsEnvironment : Bool)
      (continuation : Option Identity) (result : Address)
  | leave (context : Context) (brand : Identity) (argument : Address)
  | primitive (context : Context) (destination : Address) (binding : RuntimeBinding)
      (arguments : List Term) (operands : List Address) (next : Code)
  | foreign (context : Context) (destination : Address) (binding : RuntimeBinding)
      (operands : List Address) (hostState : List Nat) (next : Code)
  | stopped (result : Address)
  | fatal (reason : Fatal)
  deriving Repr, Inhabited

inductive Frame where
  | binding (caller : Context) (destination : Address) (next : Code)
  | activation (caller : Context) (activation region : Identity)
  | scope (outer : Context) (scope region : Identity)
  | label (outer : Context) (brand region : Identity) (result : Term)
  | handler (handler : InstalledHandler) (ownsEnvironment : Bool)
  | serviced (handler : InstalledHandler) (ownsEnvironment : Bool) (clause : Context)
      (continuation : Option Identity)
  | completion (handler : InstalledHandler) (ownsEnvironment : Bool) (clause : Context)
  | resumed (caller : Context)
  | tailResume (caller : Context) (continuation : Identity)
  | hook (context : Context) (address : Address) (authority : Authority)
      (handle : Address) (loan : Identity) (next : Task)
  | foreign (identity : Identity)
  | hostCallback (context : Context) (destination : Address) (binding : RuntimeBinding)
      (operands : List Address) (hostState : List Nat) (next : Code)
  deriving Repr, Inhabited

def Frame.ownedRegions : Frame → List Identity
  | .activation _ _ region | .scope _ _ region => [region]
  | .handler installed owns => installed.computation.region :: (if owns then [installed.environment.region] else [])
  | .serviced installed owns clause _ | .completion installed owns clause =>
      clause.region :: (if owns then [installed.environment.region] else [])
  | _ => []

def CloseRegions (regions : List Identity) (next : Task) : Task := regions.eraseDups.foldr Task.closeRegion next

structure Suspension where
  identity : Identity
  handler : InstalledHandler
  frames : List Frame
  context : Context
  roots : List Identity
  homes : Table Home
  quantity : Quantity
  remaining : Nat
  used : Nat
  original : Bool
  active : Bool
  deriving Repr, Inhabited

structure State where
  world : World
  task : Task
  frames : List Frame := []
  resumptions : Table Suspension := []
  nextActivation : Identity := 0
  nextHandler : Identity := 0
  nextBrand : Identity := 0
  nextContinuation : Identity := 0
  deriving Repr, Inhabited

inductive Event where
  | allocate (address : Address)
  | move (source destination : Address)
  | copy (source destination : Address)
  | borrow (referent : Address) (loan : Identity)
  | loanEnd (loan : Identity)
  | shellConsumed (address : Address)
  | hookEnter (address : Address) (declaration : DeclId)
  | destroy (address : Address) (owner : Identity)
  | retire (root : Identity)
  | call (declaration : DeclId) (inputs : List InvocationInput)
  | tail (fromActivation toActivation : Identity)
  | branch (pattern : Identity) (positive : Bool)
  | perform (operation : DeclId) (instanceArguments : List Term)
  | suspend (continuation : Identity)
  | replay (continuation : Identity) (last : Bool)
  | cancel (continuation : Identity)
  | leave (brand : Identity)
  | host (symbol : String) (input output : List Nat)
  | fatal (reason : Fatal)
  deriving Repr, Inhabited

def Temporary (program : Kernel.Program) (context : Context) (type : Term)
    (before : World) (address : Address) (after : World) : Prop :=
  ∃ layout, Allocates program.declarations before (.temporary context.activation context.scope)
    context.region type layout true address after

def Protect (program : Kernel.Program) (outer : Context) (before : World)
    (source : Address) (authority : Authority) (destination : Address) (after : World) : Prop :=
  ∃ value allocated, before.Stores source value ∧ Temporary program outer value.type before destination allocated ∧
    Transfers allocated authority source destination after

def RegionCanEnd (world : World) (region : Identity) : Prop :=
  (∀ id root, world.roots.get id = some root → root.live = true → root.region ≠ region) ∧
  (∀ id loan, world.loans.get id = some loan → loan.live = true → loan.region ≠ region) ∧
  (∀ id available, world.availability.get id = some available → available.active = true → available.region ≠ region)

def RegionEnds (before : World) (region : Identity) (after : World) : Prop :=
  RegionCanEnd before region ∧ after = { before with liveRegions := before.liveRegions.filter (· != region) }

inductive Addresses (world : World) (environment : Environment) : List Place → List Address → Prop where
  | nil : Addresses world environment [] []
  | cons {place places address authority addresses} : ResolvesPlace world environment place address authority →
      Permitted world authority .shared address → Addresses world environment places addresses →
      Addresses world environment (place :: places) (address :: addresses)

inductive ArgumentInputs (world : World) (context : Context) :
    Nat → List Local → List Place → List InvocationInput → Prop where
  | nil {index} : ArgumentInputs world context index [] [] []
  | cons {index formal formals place places address authority rest} :
      ResolvesPlace world context.environment place address authority → world.Initialized address →
      ArgumentInputs world context (index+1) formals places rest →
      ArgumentInputs world context index (formal :: formals) (place :: places)
        (⟨.argument index,formal,address,authority,.owned⟩ :: rest)

def CaptureInputs (world : World) (receiver : Address) (authority : Authority) (access : Access)
    (formals : List Local) (inputs : List InvocationInput) : Prop :=
  inputs = formals.zipIdx.map (fun (formal,index) => ⟨.capture index,formal,receiver.child index,authority,access⟩) ∧
  ∀ input ∈ inputs, world.Initialized input.storage ∧ Permitted world input.authority access input.storage

def CallableReceiver (world : World) (address : Address) (authority : Authority) (access : Access)
    (id : DeclId) (arguments : List Term) : Prop :=
  ∃ value, world.Stores address value ∧ value.Initialized ∧ value.head = .callable id arguments ∧
    Permitted world authority access address

inductive ConsumesReceiver : World → Address → Authority → Access → World → Prop where
  | lent {world address authority access} : access ≠ .owned → ConsumesReceiver world address authority access world
  | owned {before address authority value after} : before.Stores address value → value.shellLive = true →
      (∃ id arguments, value.head = .callable id arguments) → Permitted before authority .owned address →
      before.write address (some (.resident value.owner value.type value.head false value.fields)) = some after →
      ConsumesReceiver before address authority .owned after

def EnterWorld (program : Kernel.Program) (before : State) (caller : Context)
    (function : Function) (inputs : List InvocationInput) (context : Context) (after : World) : Prop :=
  ∃ withRegion environment declaration,
    program.declarations.function function.declaration = some declaration ∧
    FreshRegion before.world before.world.nextRegion withRegion ∧
    BindsInputs program.declarations before.nextActivation before.world.nextRegion before.world.nextRegion
      withRegion inputs environment after ∧
    context = ⟨environment,declaration.header.module,before.nextActivation,before.world.nextRegion,before.world.nextRegion,
      function.entryScope before.world.nextRegion before.nextBrand,false⟩ ∧
    (function.signature.unsafeAllowed = true → caller.unsafeAllowed = true)

def FreshNamedFrame (function : Function) (caller : Context) (brand region : Identity) : List Frame :=
  match function.namedExit with
  | none => []
  | some _ => [.label caller brand region function.signature.result]

/-- A proper-tail destination has no outstanding result transformation or
dynamic delimiter. More permissive structural fusion requires a separate
equivalence proof in the target contract, not a retained old activation. -/
inductive TailFrames : List Frame → Identity → Context → List Identity → List Frame → Prop where
  | activation {caller activation region rest} : TailFrames (.activation caller activation region :: rest) activation caller [region] rest
  | scope {outer scope region rest activation caller regions finish} :
      TailFrames rest activation caller regions finish →
      TailFrames (.scope outer scope region :: rest) activation caller (region :: regions) finish
  | label {outer brand region result rest activation caller regions finish} :
      TailFrames rest activation caller regions finish →
      TailFrames (.label outer brand region result :: rest) activation caller regions finish

def ScheduledPattern (actions : PatternActions) : List PatternAction :=
  actions.shells ++ actions.bindings ++ actions.cleanup

inductive LocalStep (program : Kernel.Program) : State → Option Event → State → Prop where
  | evaluate {before context lexical localSlot value next address allocated layout} :
      before.task = .run context (.evaluate lexical value next) → localSlot = context.local lexical →
      Allocates program.declarations before.world (.localSlot context.activation context.scope) context.region
        localSlot.type layout localSlot.mutable address allocated →
      LocalStep program before (some (.allocate address))
        { before with world := allocated, task := .run context value, frames := .binding (context.bind localSlot address) address next :: before.frames }
  | bind {before context lexical localSlot atom next address allocated layout} :
      before.task = .run context (.bind lexical atom next) → localSlot = context.local lexical →
      Allocates program.declarations before.world (.localSlot context.activation context.scope) context.region
        localSlot.type layout localSlot.mutable address allocated →
      LocalStep program before (some (.allocate address))
        { before with world := allocated, task := .atom (context.bind localSlot address) address (atom.mapTerms context.term) next }
  | result {before context place address authority value kept after} : before.task = .run context (.result place) →
      ResolvesPlace before.world context.environment place address authority → before.world.Stores address value →
      Protect program context before.world address authority kept after →
      LocalStep program before (some (.move address kept))
        { before with world := after, task := .yield context kept }
  | discard {before context place next address authority} : before.task = .run context (.discard place next) →
      ResolvesPlace before.world context.environment place address authority →
      LocalStep program before none { before with task := .destroy context address authority (.run context next) }
  | assign {before context destination source next target permission value authority} :
      before.task = .run context (.assign destination source next) →
      ResolvesPlace before.world context.environment destination target permission →
      ResolvesPlace before.world context.environment source value authority →
      Permitted before.world permission .unique target → ¬ target.Overlaps value →
      LocalStep program before none { before with task := .destroy context target permission (.transfer value authority target (.run context next)) }
  | transfer {before source authority destination next after} : before.task = .transfer source authority destination next →
      Transfers before.world authority source destination after →
      LocalStep program before (some (.move source destination)) { before with world := after, task := next }
  | invoke {before context lexical result call next destination allocated layout} :
      before.task = .run context (.invoke lexical call next) → result = context.local lexical →
      Allocates program.declarations before.world (.localSlot context.activation context.scope) context.region
        result.type layout result.mutable destination allocated →
      LocalStep program before (some (.allocate destination)) { before with world := allocated, task := .apply context (context.invocation call) false, frames := .binding (context.bind result destination) destination next :: before.frames }
  | tailRequest {before context call} : before.task = .run context (.tail call) →
      LocalStep program before none { before with task := .apply context (context.invocation call) true }
  | call {before context call tail receiver authority id arguments function captures inputs consumed} :
      before.task = .apply context call tail →
      ResolvesPlace before.world context.environment call.callee receiver authority →
      CallableReceiver before.world receiver authority call.receiver id arguments → Instance program id arguments function →
      function.signature = call.signature → CaptureInputs before.world receiver authority call.receiver function.captures captures →
      ArgumentInputs before.world context 0 function.parameters call.arguments inputs →
      ConsumesReceiver before.world receiver authority call.receiver consumed →
      LocalStep program before (some (.call id (captures ++ inputs)))
        { before with world := consumed, task := .enter context function (captures ++ inputs) tail }
  | enter {before caller function inputs context after} : before.task = .enter caller function inputs false →
      EnterWorld program before caller function inputs context after →
      LocalStep program before none { before with world := after, task := .run context function.body, frames := FreshNamedFrame function context before.nextBrand context.region ++ .activation caller context.activation context.region :: before.frames, nextActivation := before.nextActivation+1, nextBrand := before.nextBrand+1 }
  | enterTail {before caller function inputs context after outer regions rest roots} :
      before.task = .enter caller function inputs true → EnterWorld program before caller function inputs context after →
      TailFrames before.frames caller.activation outer regions rest →
      ActivationRoots after caller.activation [] roots → Suspensible after roots →
      (∀ input ∈ inputs, input.access ≠ .owned → input.storage.root ∉ roots) →
      LocalStep program before (some (.tail caller.activation context.activation)) { before with world := after, task := .cleanup caller roots (CloseRegions regions (.run context function.body)), frames := FreshNamedFrame function context before.nextBrand context.region ++ .activation outer context.activation context.region :: rest, nextActivation := before.nextActivation+1, nextBrand := before.nextBrand+1 }
  | bindReturn {before context value caller destination next rest after} : before.task = .yield context value →
      before.frames = .binding caller destination next :: rest → Transfers before.world .owner value destination after →
      LocalStep program before (some (.move value destination))
        { before with world := after, task := .retire value.root (.run caller next), frames := rest }
  | activationReturn {before context value outer activation region rest kept after roots} :
      before.task = .yield context value → before.frames = .activation outer activation region :: rest →
      context.activation = activation → Protect program outer before.world value .owner kept after →
      ActivationRoots after activation [] roots → Suspensible after roots →
      LocalStep program before none { before with world := after, task := .cleanup context roots (.closeRegion region (.yield outer kept)), frames := rest }
  | topReturn {before context value} : before.task = .yield context value → before.frames = [] →
      LocalStep program before none { before with task := .stopped value }
  | scope {before context identity body after inner} : before.task = .run context (.scope identity body) →
      FreshRegion before.world before.world.nextRegion after →
      inner = { context.bindRegion identity before.world.nextRegion with scope := before.world.nextRegion, region := before.world.nextRegion } →
      LocalStep program before none { before with world := after, task := .run inner body, frames := .scope context inner.scope inner.region :: before.frames }
  | scopeReturn {before context value outer scope region rest kept after roots} : before.task = .yield context value →
      before.frames = .scope outer scope region :: rest → Protect program outer before.world value .owner kept after →
      ScopeRoots after context.activation scope [] roots → Suspensible after roots →
      LocalStep program before none { before with world := after, task := .cleanup context roots (.closeRegion region (.yield outer kept)), frames := rest }
  | label {before context lexical region result body inner} : before.task = .run context (.label lexical region result body) →
      inner = (context.bindRegion region context.region).bindBrand lexical (.label before.nextBrand) →
      LocalStep program before none { before with task := .run inner body, frames := .label context before.nextBrand context.region (inner.term result) :: before.frames, nextBrand := before.nextBrand+1 }
  | labelReturn {before context value outer brand region result rest} : before.task = .yield context value →
      before.frames = .label outer brand region result :: rest →
      LocalStep program before none { before with task := .yield outer value, frames := rest }
  | choose {before context subject arms address authority arm actions} : before.task = .run context (.choose subject arms) →
      ResolvesPlace before.world context.environment subject address authority →
      FirstArm program.declarations before.world address arms arm →
      PatternPlan program.declarations before.world address authority .owned (arm.pattern.mapTerms context.term) actions →
      LocalStep program before none { before with task := .pattern context (ScheduledPattern actions) arm.body }
  | patternDone {before context body} : before.task = .pattern context [] body →
      LocalStep program before none { before with task := .run context body }
  | patternBind {before context localSlot address authority access rest body binding after} :
      before.task = .pattern context (.bind localSlot address authority access :: rest) body →
      BindsInput program.declarations context.activation context.scope context.region before.world
        ⟨.argument 0,localSlot,address,authority,access⟩ binding after →
      LocalStep program before none { before with world := after, task := .pattern (context.bind localSlot binding.address binding.authority) rest body }
  | patternShell {before context address authority rest body after} :
      before.task = .pattern context (.consumeShell address authority :: rest) body →
      Deconstructs program.declarations context.static before.world authority address after →
      LocalStep program before (some (.shellConsumed address))
        { before with world := after, task := .pattern context rest body }
  | patternDispose {before context address authority rest body} :
      before.task = .pattern context (.dispose address authority :: rest) body →
      LocalStep program before none { before with task := .destroy context address authority (.pattern context rest body) }
  | unsafeAllowed {before context body} : before.task = .run context (.unsafeScope body) →
      LocalStep program before none { before with task := .run { context with unsafeAllowed := true } body }
  | cleanupDone {before context next} : before.task = .cleanup context [] next →
      LocalStep program before none { before with task := next }
  | cleanupRoot {before context id roots next root} : before.task = .cleanup context (id :: roots) next →
      before.world.roots.get id = some root → root.live = true →
      LocalStep program before none { before with task := .destroy context ⟨id,root.generation,[]⟩ .owner (.retire id (.cleanup context roots next)) }
  | destroyVacant {before context address authority next} : before.task = .destroy context address authority next →
      before.world.Vacant address → LocalStep program before none { before with task := next }
  | destroyHook {before context address authority next value hook function withHandle handle after loan} :
      before.task = .destroy context address authority next → before.world.Stores address value → value.shellLive = true →
      MayDispose program.declarations value → DropHook program.declarations value.type (some hook) →
      Instance program hook [] function → function.parameters.length = 1 → function.captures = [] →
      Temporary program context (.reference .unique (.runtimeRegion context.region) value.type) before.world handle withHandle →
      Borrows program.declarations withHandle authority .unique context.region address handle after → loan = withHandle.nextLoan →
      LocalStep program before (some (.hookEnter address hook)) { before with world := after, task := .enter { context with unsafeAllowed := false } function [⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩] false, frames := .hook context address authority handle loan next :: before.frames }
  | hookReturned {before context result outer address authority handle loan next rest} : before.task = .yield context result →
      before.frames = .hook outer address authority handle loan next :: rest →
      LocalStep program before none { before with frames := rest, task := .destroy outer result .owner (.retire result.root (.retire handle.root (.closeLoan loan (.destroyFields outer address authority (match before.world.read address with | none => [] | some value => (List.range value.fields.length).reverse) next)))) }
  | destroyStructural {before context address authority next value} : before.task = .destroy context address authority next →
      before.world.Stores address value → MayDispose program.declarations value → Permitted before.world authority .owned address →
      (value.shellLive = false ∨ DropHook program.declarations value.type none) →
      (∀ id, value.head ≠ .continuation id) → (∀ id, value.head ≠ .reference id) →
      (∀ id, value.head ≠ .available id) →
      LocalStep program before none { before with task := .destroyFields context address authority (List.range value.fields.length).reverse next }
  | destroyReference {before context address authority next value id cleared following} :
      before.task = .destroy context address authority next → before.world.Stores address value → value.head = .reference id →
      MayDispose program.declarations value → Permitted before.world authority .owned address →
      before.world.write address none = some cleared →
      (cleared.References id ∧ following = next ∨ ¬ cleared.References id ∧ following = .closeLoan id next) →
      LocalStep program before (some (.destroy address value.owner)) { before with world := cleared, task := following }
  | fieldsDone {before context address authority next} : before.task = .destroyFields context address authority [] next →
      LocalStep program before none { before with task := .finishShell address next }
  | fieldNext {before context address authority field fields next} :
      before.task = .destroyFields context address authority (field :: fields) next →
      LocalStep program before none { before with task := .destroy context (address.child field) authority (.destroyFields context address authority fields next) }
  | shellDone {before address next value after} : before.task = .finishShell address next →
      before.world.Stores address value → (∀ field ∈ value.fields, field = none) →
      before.world.write address none = some after →
      LocalStep program before (some (.destroy address value.owner)) { before with world := after, task := next }
  | retire {before id next after} : before.task = .retire id next → Retires before.world id after →
      LocalStep program before (some (.retire id)) { before with world := after, task := next }
  | regionEnd {before region next after} : before.task = .closeRegion region next → RegionEnds before.world region after →
      LocalStep program before none { before with world := after, task := next }
  | loanEnd {before id next after} : before.task = .closeLoan id next → EndsLoan before.world id after →
      LocalStep program before (some (.loanEnd id)) { before with world := after, task := next }
  | loanAlreadyEnded {before id next loan} : before.task = .closeLoan id next →
      before.world.loans.get id = some loan → loan.live = false →
      LocalStep program before none { before with task := next }
  | endLoan {before context handle next address authority value id} : before.task = .run context (.endLoan handle next) →
      ResolvesPlace before.world context.environment handle address authority → before.world.Stores address value →
      value.head = .reference id →
      LocalStep program before none { before with task := .destroy context address authority (.closeLoan id (.run context next)) }
  | abort {before context} : before.task = .run context .abort →
      LocalStep program before (some (.fatal .abort)) { before with task := .fatal .abort }

end Glorious.Language.Execution
