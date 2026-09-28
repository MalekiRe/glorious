 import GloriousLanguage.Typing
 import GloriousLanguage.ControlOrigin
 import GloriousLanguage.InvocationInputs
 import GloriousLanguage.LabelBoundary
 import GloriousLanguage.ForeignRuntimeSupport
 import GloriousLanguage.TailEntryProgress
 import GloriousLanguage.CopyProgress
import GloriousLanguage.ProjectionResolution

/-! Checked interfaces are abstractions of execution, not trusted annotations.
The meaning below is intentionally semantic; it does not claim that an
arbitrary exact control contract has a decidable inference procedure. -/
namespace Glorious.Language.Contracts

open Kernel Execution

inductive Outcome where
  | normal (result : Address)
  | label (brand : Identity) (result : ResolvedPlace)
  | operation (id : DeclId) (arguments : List Term) (payload : List ResolvedPlace)
  | fault (reason : Fatal)
  | divergent
  | unknown
  deriving Repr, Inhabited

inductive Guard where
  | always
  | constructor (origin : Identity) (path : List Nat) (variant : DeclId)
  | pattern (origin pattern : Identity) (positive : Bool)
  | and (left right : Guard)
  | or (left right : Guard)
  deriving Repr, Inhabited

def Guard.Holds (world : World) : Guard → Prop
  | .always => True
  | .constructor origin path variant => ∃ address value selected,
      world.Resident address value ∧ value.owner = origin ∧ value.atPath path = some selected ∧ selected.head = .constructor variant
  | .pattern origin patternId positive => ∃ address value pack,
      world.Resident address value ∧ value.shellLive = true ∧ value.head = .bindings pack ∧
      ⟨origin,patternId,positive⟩ ∈ pack.facts
  | .and left right => left.Holds world ∧ right.Holds world
  | .or left right => left.Holds world ∨ right.Holds world

structure Observation where
  input : List InvocationInput
  before : World
  events : List Event
  after : World
  outcome : Outcome

def InputsTyped (program : Kernel.Program) (inputs : List InvocationInput) (world : World) : Prop :=
  Typing.WorldTyped program world ∧
  (inputs.map (fun input => input.formal.key)).Nodup ∧
  InvocationInputsReady program world inputs

/-- Source locals retain their ordered capture/argument coordinates. Erased
storage ports remain the actual common inputs with obligation identities,
not invented resident locals. The same authority-independent projection is
preserved by ordinary receiver preparation. -/
def FunctionInputs (function : Function) (inputs : List InvocationInput) : Prop :=
  let coordinates := inputs.map (fun input => (input.formal,input.origin,input.access))
  let residents := coordinates.filter (fun coordinate => coordinate.1.resident?.isSome)
  residents.map Prod.fst = (function.captures ++ function.parameters).map InputFormal.resident ∧
  (∀ index formal origin access, residents[index]? = some (formal,origin,access) →
    (index < function.captures.length ∧ origin = .capture index) ∨
      (function.captures.length ≤ index ∧ origin = .argument (index-function.captures.length) ∧ access = .owned)) ∧
  (∀ coordinate ∈ coordinates, ¬ coordinate.1.IsResident →
    ∃ identity, coordinate.2.1 = .obligation identity ∧ coordinate.1.key = .resourceInput identity)

/-- A capture-free unary body consumes the same resident coordinate filter
as every invocation, with no invented raw obligation port. -/
theorem FunctionInputs.argument {function : Function} {formal : Local} {address : Address}
    {authority : Authority} (captures : function.captures = []) (parameters : function.parameters = [formal]) :
    FunctionInputs function [⟨.argument 0,formal,address,authority,.owned⟩] := by
  change [InputFormal.resident formal] = (function.captures ++ function.parameters).map InputFormal.resident ∧
    (∀ index input origin access,
      [(InputFormal.resident formal,InvocationOrigin.argument 0,Access.owned)][index]? = some (input,origin,access) →
      (index < function.captures.length ∧ origin = .capture index) ∨
        (function.captures.length ≤ index ∧ origin = .argument (index-function.captures.length) ∧ access = .owned)) ∧
    (∀ coordinate ∈ [(InputFormal.resident formal,InvocationOrigin.argument 0,Access.owned)],
      ¬ coordinate.1.IsResident → ∃ identity, coordinate.2.1 = .obligation identity ∧ coordinate.1.key = .resourceInput identity)
  refine ⟨by rw [captures,parameters]; rfl,?_,?_⟩
  · intro index input origin access found
    cases index with
    | zero =>
      cases Option.some.inj found
      exact Or.inr ⟨by simp [captures],by simp [captures],rfl⟩
    | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil,reduceCtorEq] at found
  · intro coordinate member erased
    have same := List.mem_singleton.mp member
    subst coordinate
    exact False.elim (erased trivial)


/-- Admission is at the actual `enter` task, before fresh-region creation,
receiver lending and ordinary input binding. Original storage/access coordinates
come from the same capture projection used by that preparation, not a fabricated
supplied-input execution. No successful entry or after-state safety is assumed. -/
def InvocationStart (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (inputs : List InvocationInput) (boundary : InvocationBoundary) (state : State) : Prop :=
  InputsTyped program inputs state.world ∧ FunctionInputs function inputs ∧ state.ControlWellFormed ∧
  host.AuthoritiesRecorded state.world state.hostState ∧ host.CallbacksWellFormed state ∧
  ∃ caller source tail, state.task = .enter caller function source tail ∧
    source.originalInputs function = inputs ∧ boundary.Entry state caller source inputs tail ∧
    caller.region ∈ state.world.liveRegions ∧
    (function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) ∧
    source.Admitted program state.world caller.region function ∧
    (tail = true → ∃ roots, source.CleanupAdmitted program state.world function caller.activation roots)
/-- A source operand before runtime resolution. This retains the Core `Place` identity and the callee's formal coordinate; it does not invent an address or authority. -/
structure SourceInput where
  place : Place
  formal : InputFormal
  origin : InvocationOrigin
  access : Access
  deriving Repr, Inhabited

/-- Realize a source operand through the same environment lookup and permission graph consumed by machine operand preparation. -/
def SourceInput.Resolves (world : World) (environment : Environment) (source : SourceInput) (input : InvocationInput) : Prop :=
  ∃ address authority, ResolvesPlace world environment source.place address authority ∧
    input = ⟨source.origin,source.formal,address,authority,source.access⟩

/-- Complete ordered input batches are checked on one pre-state. -/
def SourceInputsCompatible (program : Kernel.Program) (function : Function) (region : Identity)
    (world : World) (environment : Environment) (sources : List SourceInput) : Prop :=
  ∃ inputs, ListRel (SourceInput.Resolves world environment) sources inputs ∧
    FunctionInputs function inputs ∧
    InvocationInputsCompatible program (inputs.flatMap InvocationInput.clearedStorage) region world inputs ∧
    IncomingResources program function world inputs ∧
    ∃ declaration, program.declarations.function function.declaration = some declaration

/-- Finite source assertions name resolved semantic places, never a second
string-keyed resource ledger. The `freshLoan` binder denotes a genuinely absent
loan identity in the interpreted pre-state. -/
inductive SourceAssertion where
  | initialized (place : Place)
  | resources (place : Place) (access : Access)
  | permission (place : Place) (access : Access)
  | selfSeparated (place : Place)
  | custody (place : Place) (kind : ClaimCustody)
  | inputBatch (operands : List SourceInput)
  | ownersOutside (active : List Place) (capturedRoots : List Address)
  | compatible (left right : SourceAssertion)
  | separating (left right : SourceAssertion)
  | guarded (guard : Guard) (assertion : SourceAssertion)
  | freshLoan (continuation : Identity → SourceAssertion)

def SourceAssertion.places : SourceAssertion → List Place
  | .inputBatch operands => operands.map SourceInput.place
  | .initialized place | .permission place _ | .resources place _ | .custody place _ => [place]
  | .selfSeparated place => [place]
  | .ownersOutside active _ => active
  | .compatible left right | .separating left right => left.places ++ right.places
  | .guarded _ assertion => assertion.places
  | .freshLoan _ => []

/-- Interpret source assertions against the actual resolving environment and
loan/resource graph. Compatible conjunction permits shared places when the
underlying permissions do; separating conjunction additionally requires
distinct resolved addresses. Guarded and fresh-identity alternatives remain
finite syntax and retain their actual semantic branch premise. -/
def SourceAssertion.Holds (program : Kernel.Program) (function : Function) (region : Identity)
    (world : World) (environment : Environment) : SourceAssertion → Prop
  | .initialized place => ∃ address authority value,
      ResolvesPlace world environment place address authority ∧ world.Stores address value ∧ value.Initialized
  | .permission place access => ∃ address authority,
      ResolvesPlace world environment place address authority ∧ Permitted world authority access address
  | .custody place kind => ∃ address authority, ResolvesPlace world environment place address authority ∧
      authority.Custodied world kind
  | .inputBatch operands => SourceInputsCompatible program function region world environment operands
  | .resources place access => ∃ address authority value,
      ResolvesPlace world environment place address authority ∧ world.Stores address value ∧ value.Initialized ∧
      value.ResourcesAccessible program world access
  | .selfSeparated place => ∃ address authority value,
      ResolvesPlace world environment place address authority ∧ world.Stores address value ∧
      value.SupportOutside world address
  | .compatible left right => left.Holds program function region world environment ∧
      right.Holds program function region world environment
  | .separating left right => left.Holds program function region world environment ∧
      right.Holds program function region world environment ∧
      (∀ first ∈ left.places, ∀ second ∈ right.places, ∀ address authority other otherAuthority,
        ResolvesPlace world environment first address authority →
        ResolvesPlace world environment second other otherAuthority → address ≠ other)
  | .guarded guard assertion => guard.Holds world → assertion.Holds program function region world environment
  | .freshLoan continuation => ∃ identity, world.loans.get identity = none ∧
      (continuation identity).Holds program function region world environment
  | .ownersOutside active capturedRoots => ∀ place ∈ active, ∀ address authority,
      ResolvesPlace world environment place address authority → authority = .owner →
        ∀ captured ∈ capturedRoots, address.root ≠ captured.root


/-- Compatible resource and permission facts for one Core place recover one
actual value/address/authority witness. -/
theorem SourceAssertion.resourcePermission {program : Kernel.Program} {function : Function} {region : Identity}
    {world : World} {environment : Environment} {place : Place} {access : Access}
    (facts : SourceAssertion.Holds program function region world environment
      (.compatible (.resources place access) (.permission place access))) :
    ∃ source authority value, ResolvesPlace world environment place source authority ∧
      world.Stores source value ∧ value.Initialized ∧ value.ResourcesAccessible program world access ∧
      Permitted world authority access source := by
  rcases facts with ⟨⟨source,authority,value,resolved,stored,initialized,resources⟩,
    ⟨target,targetAuthority,targetResolved,permission⟩⟩
  obtain ⟨rfl,rfl⟩ := ResolvesPlace.deterministic resolved targetResolved
  exact ⟨source,authority,value,resolved,stored,initialized,resources,permission⟩

/-- Owned movement additionally requires that the current value's support graph
does not point back into its own source storage. -/
theorem SourceAssertion.resourceMoveFacts {program : Kernel.Program} {function : Function} {region : Identity}
    {world : World} {environment : Environment} {place : Place}
    (facts : SourceAssertion.Holds program function region world environment
      (.compatible (.resources place .owned)
        (.compatible (.permission place .owned) (.selfSeparated place)))) :
    ∃ source authority value, ResolvesPlace world environment place source authority ∧
      world.Stores source value ∧ value.Initialized ∧ value.ResourcesAccessible program world .owned ∧
      Permitted world authority .owned source ∧ value.SupportOutside world source := by
  rcases facts with ⟨resourceFacts,⟨permissionFacts,separationFacts⟩⟩
  have combined : SourceAssertion.Holds program function region world environment
      (.compatible (.resources place .owned) (.permission place .owned)) :=
    ⟨resourceFacts,permissionFacts⟩
  rcases SourceAssertion.resourcePermission combined with
    ⟨source,authority,value,resolved,stored,initialized,accessible,permission⟩
  rcases separationFacts with ⟨separated,separatedAuthority,separatedValue,separatedResolved,separatedStored,supportOutside⟩
  obtain ⟨rfl,rfl⟩ := ResolvesPlace.deterministic resolved separatedResolved
  have sameValue : value = separatedValue := by
    exact Option.some.inj (stored.symm.trans separatedStored)
  subst sameValue
  exact ⟨source,authority,value,resolved,stored,initialized,accessible,permission,supportOutside⟩

/-- The source acquisition rule derives the selected copy/move premises from
the prior initialized resource, permission and provenance assertions. The
actual destination is chosen only by the positive allocation request. -/
theorem SourceAssertion.acquireAllocation {program : Kernel.Program} {function : Function} {region : Identity}
    {before : World} {environment : Environment} {place : Place} {home : Home}
    {type : Term} {layout : Layout} {mutable : Bool} {force : Bool} {principal : Principal}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (capability : ∀ source authority value, ResolvesPlace before environment place source authority →
      before.Stores source value → PrincipalOf program.declarations value.type principal)
    (sourceType : ∀ source authority value, ResolvesPlace before environment place source authority →
      before.Stores source value → value.type = type)
    (copyFacts : force = false → principal = .duplicable →
      SourceAssertion.Holds program function region before environment
        (.compatible (.resources place .shared) (.permission place .shared)))
    (moveFacts : force = true ∨ principal ≠ .duplicable →
      SourceAssertion.Holds program function region before environment
        (.compatible (.resources place .owned)
          (.compatible (.permission place .owned) (.selfSeparated place))))
    (request : AllocationRequest program.declarations before region type layout) :
    (∃ destination allocated after,
      Allocates program.declarations before home region type layout mutable destination allocated ∧
      ∃ source authority value, ResolvesPlace before environment place source authority ∧
        before.Stores source value ∧ PrincipalOf program.declarations value.type principal ∧
        Acquires program allocated authority force source destination after ∧ Typing.WorldTyped program after ∧
        ∃ result, after.Stores destination result ∧ result.Initialized ∧
          result.ResourcesAccessible program after .owned) ∨
      AllocationExhausted program.declarations before region type layout := by
  by_cases copying : force = false ∧ principal = .duplicable
  · obtain ⟨rfl,rfl⟩ := copying
    obtain ⟨source,authority,value,resolved,stored,initialized,accessible,permission⟩ :=
      SourceAssertion.resourcePermission (copyFacts rfl rfl)
    have capability := capability source authority value resolved stored
    have valueType := sourceType source authority value resolved stored
    subst type
    have copyReady : false = false → Principal.duplicable = .duplicable →
        value.ResourcesAccessible program before .shared ∧ Permitted before authority .shared source := by
      intro _ _
      exact ⟨accessible,permission⟩
    have moveReady : false = true ∨ Principal.duplicable ≠ .duplicable →
        value.MoveReady program before [source] ∧ Permitted before authority .owned source := by
      intro impossible
      rcases impossible with forceTrue | nonduplicable
      · cases forceTrue
      · exact False.elim (nonduplicable rfl)
    rcases Acquires.allocate_success_or_exhausted valid inventory typed stored initialized capability
      copyReady moveReady request with ⟨destination,allocated,after,allocation,acquired,afterTyped,result⟩ | exhausted
    · exact Or.inl ⟨destination,allocated,after,allocation,source,authority,value,resolved,stored,capability,acquired,afterTyped,result⟩
    · exact Or.inr exhausted
  · have moving : force = true ∨ principal ≠ .duplicable := by
      cases force with
      | true => exact Or.inl rfl
      | false => exact Or.inr (fun same => copying ⟨rfl,same⟩)
    obtain ⟨source,authority,value,resolved,stored,initialized,accessible,permission,supportOutside⟩ :=
      SourceAssertion.resourceMoveFacts (moveFacts moving)
    have capability := capability source authority value resolved stored
    have valueType := sourceType source authority value resolved stored
    subst type
    have copyReady : force = false → principal = .duplicable →
        value.ResourcesAccessible program before .shared ∧ Permitted before authority .shared source := by
      intro forced duplicate
      exact False.elim (copying ⟨forced,duplicate⟩)
    have moveReady : force = true ∨ principal ≠ .duplicable →
        value.MoveReady program before [source] ∧ Permitted before authority .owned source := by
      intro _
      have ready : value.MoveReady program before [source] := by
        change value.HandoffReady program before .owned [source]
        refine ⟨accessible,?_⟩
        intro target member
        have same := List.mem_singleton.mp member
        subst target
        exact supportOutside
      exact ⟨ready,permission⟩
    rcases Acquires.allocate_success_or_exhausted valid inventory typed stored initialized capability
      copyReady moveReady request with ⟨destination,allocated,after,allocation,acquired,afterTyped,result⟩ | exhausted
    · exact Or.inl ⟨destination,allocated,after,allocation,source,authority,value,resolved,stored,capability,acquired,afterTyped,result⟩
    · exact Or.inr exhausted
/-- The allocation/acquisition post-value is visible through the actual
shadowing local binding installed by Core's `.bind` step. -/
theorem SourceAssertion.boundDestination {program : Kernel.Program} {function : Function} {region : Identity}
    {context : Execution.Context} {localSlot : Local} {world : World} {address : Address} {value : Value}
    (stored : world.Stores address value) (initialized : value.Initialized)
    (resources : value.ResourcesAccessible program world .owned) :
    SourceAssertion.Holds program function region world
      (context.bind localSlot address).environment (.resources ⟨localSlot.id,[]⟩ .owned) := by
  refine ⟨address,.owner,value,?_,stored,initialized,resources⟩
  apply ResolvesPlace.localSlot
  · change (context.bind localSlot address).environment.Selects localSlot.id
      ⟨.localSlot localSlot.id,address,.owner⟩
    simp [Execution.Context.bind,Environment.Selects,Environment.SelectsKey]
    intro other member notKey selectedKey
    change (!(other.key == BindingKey.localSlot localSlot.id)) = true at notKey
    have keyEqual : (other.key == BindingKey.localSlot localSlot.id) = true := by
      rw [selectedKey]
      change (localSlot.id == localSlot.id) = true
      exact BEq.rfl
    rw [keyEqual] at notKey
    cases notKey
  · change ResolvesProjections world (context.bind localSlot address).environment address .owner [] address .owner
    exact .nil
theorem SourceAssertion.bind_preserves_selection {context : Execution.Context} {localSlot : Local}
    {address : Address} {id : Identity} {binding : Binding}
    (fresh : ∀ previous ∈ context.environment, previous.key ≠ .localSlot localSlot.id)
    (selected : context.environment.Selects id binding) :
    (context.bind localSlot address).environment.Selects id binding := by
  have different := fresh binding selected.1
  have ids : id ≠ localSlot.id := by
    intro same
    exact different (selected.2.1.trans (congrArg BindingKey.localSlot same))
  refine ⟨?_,selected.2.1,?_⟩
  · simp only [Execution.Context.bind, List.mem_cons, List.mem_filter]
    refine Or.inr ⟨selected.1,?_⟩
    rw [selected.2.1]
    change (!(id == localSlot.id)) = true
    simp [ids]
  · intro other member key
    change other ∈ _ :: _ at member
    rcases List.mem_cons.mp member with rfl | old
    · exact False.elim (ids (BindingKey.localSlot.inj key).symm)
    · exact selected.2.2 other (List.mem_filter.mp old).1 key

/-- A source acquisition binding executes allocation and acquisition in order,
then interprets its output in the actual continuation environment. Exhaustion
is the existing fatal transition of that same allocation request. -/
theorem SourceAssertion.bindAcquire {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {before : State} {context : Execution.Context} {lexical : Local}
    {place : Place} {next : Code} {layout : Layout} {force : Bool} {principal : Principal}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .run context (.bind lexical (.acquire place force) next))
    (fresh : ∀ binding ∈ context.environment, binding.key ≠ .localSlot lexical.id)
    (capability : ∀ source authority value, ResolvesPlace before.world context.environment place source authority →
      before.world.Stores source value → PrincipalOf program.declarations value.type principal)
    (sourceType : ∀ source authority value, ResolvesPlace before.world context.environment place source authority →
      before.world.Stores source value → value.type = (context.local lexical).type)
    (copyFacts : force = false → principal = .duplicable →
      SourceAssertion.Holds program function context.region before.world context.environment
        (.compatible (.resources place .shared) (.permission place .shared)))
    (moveFacts : force = true ∨ principal ≠ .duplicable →
      SourceAssertion.Holds program function context.region before.world context.environment
        (.compatible (.resources place .owned)
          (.compatible (.permission place .owned) (.selfSeparated place))))
    (request : AllocationRequest program.declarations before.world context.region (context.local lexical).type layout) :
    (∃ address event after, Run program host before [.allocate address,event] after ∧
      after.task = .run (context.bind (context.local lexical) address) next ∧
      after.frames = before.frames ∧ Typing.WorldTyped program after.world ∧
      SourceAssertion.Holds program function context.region after.world
        (context.bind (context.local lexical) address).environment (.resources ⟨lexical.id,[]⟩ .owned)) ∨
    Run program host before [.fatal .resource] {before with task := .fatal .resource} := by
  rcases SourceAssertion.acquireAllocation
    (home := .localSlot context.activation context.scope) (mutable := (context.local lexical).mutable)
    valid inventory typed capability sourceType copyFacts moveFacts request with
    ⟨address,allocated,after,allocation,source,authority,value,resolved,stored,capable,acquired,afterTyped,result⟩ | exhausted
  · have selection : ∀ id binding, context.environment.Selects id binding →
        (context.bind (context.local lexical) address).environment.Selects id binding := by
      intro id binding selected
      exact SourceAssertion.bind_preserves_selection fresh selected
    have resolution := resolved.transport selection
      (fun address _ stored => (allocation.read typed.1 address).trans stored) allocation.loans
    let middle : State := {before with world := allocated, task := .atom (context.bind (context.local lexical) address) address (.acquire place force) next}
    have allocatedStep : LocalStep program before (some (.allocate address)) middle :=
      LocalStep.bind task rfl allocation
    have acquiredStep := AtomStep.acquire (before := middle) rfl resolution acquired
    obtain ⟨output,outputStored,initialized,resources⟩ := result
    refine Or.inl ⟨address,_,_,.visible (Or.inl allocatedStep)
      (.visible (Or.inr (Or.inl acquiredStep)) .refl),rfl,rfl,afterTyped,?_⟩
    exact SourceAssertion.boundDestination outputStored initialized resources
  · exact Or.inr (.visible (Or.inl (LocalStep.bindExhausted task rfl exhausted)) .refl)

theorem SourceInputsCompatible.supplied {program : Kernel.Program} {function : Function}
    {region : Identity} {world : World} {environment : Environment} {sources : List SourceInput}
    (compatible : SourceInputsCompatible program function region world environment sources) :
    ∃ inputs, ListRel (SourceInput.Resolves world environment) sources inputs ∧
      FunctionInputs function inputs ∧
      (Execution.EntrySource.supplied inputs).Admitted program world region function := by
  obtain ⟨inputs,resolves,formals,product,incoming,declared⟩ := compatible
  exact ⟨inputs,resolves,formals,Execution.EntrySource.Admitted.supplied product incoming declared⟩

/-- A checked source input batch drives the actual ordered callee-region and
binding attempt from the current world; it is not an admitted successful entry. -/
theorem SourceInputsCompatible.enterWorldAttempt {program : Kernel.Program}
    {function : Function} {region : Identity} {world : World} {environment : Environment}
    {sources : List SourceInput} {state : State} {caller : Execution.Context}
    (compatible : SourceInputsCompatible program function region world environment sources)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program world) (sameWorld : state.world = world)
    (sameRegion : region = caller.region)
    (callerUnsafe : function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) :
    ∃ inputs, ListRel (SourceInput.Resolves world environment) sources inputs ∧
      FunctionInputs function inputs ∧
      ∃ context after outcome, EnterWorldAttempt program state caller function
        (.supplied inputs) context after outcome := by
  obtain ⟨inputs,resolves,formals,product,incoming,declared⟩ := compatible
  subst sameWorld
  subst sameRegion
  let admitted := Execution.EntrySource.Admitted.supplied product incoming declared
  exact ⟨inputs,resolves,formals,Execution.EntrySource.Admitted.enterWorldAttempt valid inventory typed admitted callerUnsafe⟩
/-- The input-batch source assertion is consumed by the actual checked entry
producer. The result exposes resolved formal rows and an ordered real
preparation attempt, not a post-entry success assumption. -/
theorem SourceAssertion.inputBatch.enterWorldAttempt {program : Kernel.Program}
    {function : Function} {region : Identity} {world : World} {environment : Environment}
    {sources : List SourceInput} {state : State} {caller : Execution.Context}
    (holds : SourceAssertion.Holds program function region world environment (.inputBatch sources))
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program world) (sameWorld : state.world = world)
    (sameRegion : region = caller.region)
    (callerUnsafe : function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) :
    ∃ inputs, ListRel (SourceInput.Resolves world environment) sources inputs ∧
      FunctionInputs function inputs ∧
      ∃ context after outcome, EnterWorldAttempt program state caller function
        (.supplied inputs) context after outcome := by
  exact SourceInputsCompatible.enterWorldAttempt holds valid inventory typed sameWorld sameRegion callerUnsafe

/-- Whole-program invocation is the isolated specialization of the same
admission relation. It retains the original supplied-input entry convention. -/
abbrev InitialInvocation (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (inputs : List InvocationInput) (state : State) : Prop :=
  InvocationStart program host function inputs .isolated state

theorem InvocationStart.isolated {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {inputs : List InvocationInput} {state : State} {caller : Execution.Context}
    (typed : InputsTyped program inputs state.world) (formals : FunctionInputs function inputs)
    (control : state.ControlWellFormed) (registry : host.AuthoritiesRecorded state.world state.hostState)
    (task : state.task = .enter caller function (.supplied inputs) false) (frames : state.frames = [])
    (region : caller.region ∈ state.world.liveRegions)
    (allowed : function.signature.unsafeAllowed = true → caller.unsafeAllowed = true)
    (admitted : (EntrySource.supplied inputs).Admitted program state.world caller.region function) :
    InitialInvocation program host function inputs state := by
  refine ⟨typed,formals,control,registry,?_,caller,.supplied inputs,false,task,rfl,⟨rfl,frames,rfl⟩,region,allowed,admitted,by intro impossible; cases impossible⟩
  constructor
  · simp only [State.CallbackControl,task,frames,Task.CallbackCovers,FramesCallbackCovers,and_self]
  · intro runtime member
    simp only [State.callbackRuntimes,task,frames,Task.callbackRuntimes,
      Foreign.AmbientRuntimes.nil,List.nil_append,List.not_mem_nil] at member

theorem InvocationStart.caller_activation_bound {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {inputs : List InvocationInput} {state : State} {caller : Execution.Context}
    {source : EntrySource} {tail : Bool} {boundary : InvocationBoundary}
    (initial : InvocationStart program host function inputs boundary state)
    (task : state.task = .enter caller function source tail) : caller.activation < state.nextActivation := by
  have bounded := initial.2.2.1.activations.task
  simpa only [task,Execution.Task.activationSupport,RootSupport.below_cons,RootSupport.below_nil,and_true] using bounded

/-- Every admitted invocation task has an actual machine successor. Ordinary
and proper-tail entry use the same original input admission, and either kind
of physical exhaustion preserves the actual successful preparation prefix. -/
theorem InvocationStart.step {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {inputs : List InvocationInput} {boundary : InvocationBoundary} {state : State}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (initial : InvocationStart program host function inputs boundary state) :
    ∃ event after, LocalStep program state event after := by
  obtain ⟨caller,source,tail,task,_,entry,_,unsafeOk,admitted,tailCleanup⟩ := initial.2.2.2.2.2
  cases tail with
  | false => exact admitted.enterStep valid inventory initial.1.1 task unsafeOk
  | true =>
      obtain ⟨roots,cleanup⟩ := tailCleanup rfl
      have different := (Nat.ne_of_lt (initial.caller_activation_bound task)).symm
      cases boundary with
      | isolated => cases entry.1
      | caller outer ambient =>
          rcases entry with ⟨impossible,_⟩ | ⟨_,regions,frames⟩
          · cases impossible
          · exact admitted.tailStep valid inventory initial.1.1 cleanup task unsafeOk different frames


/-- The real prepared input binder consumes the same ordered formal/origin
contract as admission, even when receiver lending changes its authorities. -/
theorem FunctionInputs.prepared {program : Kernel.Program} {context : Execution.Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (original : FunctionInputs function (source.originalInputs function))
    (prepared : PreparesEntry program context function before source inputs after) : FunctionInputs function inputs := by
  unfold FunctionInputs at original ⊢
  rw [prepared.map_inputs (fun input => (input.formal,input.origin,input.access)) (by intros; rfl)]
  exact original

theorem InvocationStart.prepared_inputs {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {original inputs : List InvocationInput} {boundary : InvocationBoundary} {state : State}
    {caller callee : Execution.Context} {source : EntrySource} {tail : Bool} {before after : World}
    (initial : InvocationStart program host function original boundary state)
    (task : state.task = .enter caller function source tail)
    (prepared : PreparesEntry program callee function before source inputs after) : FunctionInputs function inputs := by
  obtain ⟨_,actual,_,entry,coordinates,_⟩ := initial.2.2.2.2.2
  have same := (Task.enter.inj (entry.symm.trans task)).2.2.1
  subst actual
  apply FunctionInputs.prepared _ prepared
  simpa only [coordinates] using initial.2.1

theorem InvocationStart.inside {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {inputs : List InvocationInput} {boundary : InvocationBoundary} {state : State}
    (initial : InvocationStart program host function inputs boundary state) : boundary.Inside program state := by
  obtain ⟨caller,source,tail,task,_,entry,_⟩ := initial.2.2.2.2.2
  cases boundary with
  | isolated => trivial
  | caller returnTo ambient =>
    refine ⟨?_,?_,?_,?_⟩
    · rcases entry with ⟨_,_,rfl⟩ | ⟨_,regions,tailFrames⟩
      · exact ⟨[],rfl⟩
      · exact tailFrames_suffix tailFrames
    · rintro ⟨context,result,pending,_⟩
      simp only [task,reduceCtorEq] at pending
    · intro context id arguments payload pending
      simp only [task,reduceCtorEq] at pending
    · intro context brand result pending
      simp only [task,reduceCtorEq] at pending

/-- Finite invocation outcomes stop at the invocation boundary. Internal
continuation creation/cancellation are trace events, not exits of the helper
which contains them. Escaped continuation lifecycle observations below retain
the actual outward request which created that continuation. -/
def AtOutcome (program : Kernel.Program) (boundary : InvocationBoundary) (state : State) : Outcome → Prop
  | .normal result => boundary.Normal state result
  | .label brand result => boundary.OutwardLabel state brand result
  | .operation id arguments payload => boundary.OutwardOperation program state id arguments payload
  | .fault reason => state.task = .fatal reason
  | .divergent | .unknown => False

def ObservationAt (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (boundary : InvocationBoundary) (start finish : State) (observation : Observation) : Prop :=
  InvocationStart program host function observation.input boundary start ∧ start.world = observation.before ∧
  InvocationRun program host boundary start observation.events finish ∧ finish.world = observation.after ∧
  AtOutcome program boundary finish observation.outcome

def Observes (program : Kernel.Program) (host : Foreign.Model) (function : Function) (observation : Observation) : Prop :=
  ∃ boundary start finish, ObservationAt program host function boundary start finish observation

/-- Cancellation initiation settles the continuation's authority and starts
its cleanup. It does not assert completion of arbitrary user destructors. -/
inductive ContinuationOutcome where
  | suspended
  | cancellationStarted
  deriving Repr, Inhabited

/-- The request trace belongs to the invocation. Lifecycle events occur in
the original caller execution and are deliberately recorded separately. -/
structure LifecycleObservation where
  request : Observation
  continuation : Identity
  callerEvents : List Event
  after : World
  outcome : ContinuationOutcome

/-- The capture is the real next step at the SAME outward request, including
the original ambient handler and foreign barriers. A fresh unrelated table
entry or an internal suspension cannot establish this product. -/
def EscapedCapture (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (request : Observation) (continuation : Identity) (captured : State) : Prop :=
  ∃ boundary start pending operation arguments payload,
    ObservationAt program host function boundary start pending request ∧
    request.outcome = .operation operation arguments payload ∧
    EffectStep program pending (some (.suspend continuation)) captured

def LifecycleAt (program : Kernel.Program) (host : Foreign.Model) (captured : State)
    (observation : LifecycleObservation) : Prop :=
  match observation.outcome with
  | .suspended => observation.callerEvents = [.suspend observation.continuation] ∧ observation.after = captured.world
  | .cancellationStarted => ∃ events canceling finish,
      observation.callerEvents = .suspend observation.continuation :: events ++ [.cancel observation.continuation] ∧
      Run program host captured events canceling ∧
      EffectStep program canceling (some (.cancel observation.continuation)) finish ∧ observation.after = finish.world

def LifecycleObserves (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (observation : LifecycleObservation) : Prop :=
  ∃ captured, EscapedCapture program host function observation.request observation.continuation captured ∧
    LifecycleAt program host captured observation

def Diverges (program : Kernel.Program) (host : Foreign.Model) (function : Function) (inputs : List InvocationInput)
    (states : Nat → State) (events : Nat → Option Event) : Prop :=
  ∃ boundary, InvocationStart program host function inputs boundary (states 0) ∧
    ∀ n, InvocationStep program host boundary (states n) (events n) (states (n+1))

structure Interface where
  finite : Observation → Prop
  infinite : List InvocationInput → (Nat → State) → (Nat → Option Event) → Prop
  lifecycle : LifecycleObservation → Prop

def Derived (program : Kernel.Program) (function : Function) (interface : Interface) : Prop :=
  (∀ host observation, Foreign.Model.Lawful program host →
    Observes program host function observation → interface.finite observation) ∧
  (∀ host inputs states events, Foreign.Model.Lawful program host →
    Diverges program host function inputs states events → interface.infinite inputs states events) ∧
  (∀ host observation, Foreign.Model.Lawful program host →
    LifecycleObserves program host function observation → interface.lifecycle observation)

def ExactInterface (program : Kernel.Program) (function : Function) : Interface :=
  ⟨fun observation => ∃ host, Foreign.Model.Lawful program host ∧ Observes program host function observation,
   fun inputs states events => ∃ host, Foreign.Model.Lawful program host ∧ Diverges program host function inputs states events,
   fun observation => ∃ host, Foreign.Model.Lawful program host ∧ LifecycleObserves program host function observation⟩

/-- An outward request has an actual ordered payload preparation and the
selected operation's permission on its callee-owned post-payload remainder.
The same permission composes with the accepting caller's residual ownership;
the caller's resources are not preemptively charged to the callee. -/
def MayAwait (program : Kernel.Program) (function : Function) (state : State)
    (boundary : InvocationBoundary := .isolated) : Prop :=
  ∃ context id arguments payload operation signature,
    state.task = .perform context id arguments payload ∧ OperationInstance program id arguments operation signature ∧
    RowSubset program.declarations context.static signature.effects function.signature.effects ∧
    (∀ source ∈ payload, state.world.Initialized source.address ∧
      Permitted state.world source.authority .owned source.address) ∧
    (¬ boundary.InternalOperation program state id arguments payload) ∧
    ∃ disposition, OperationDisposition.Matches operation disposition ∧
      boundary.OperationReady program state payload disposition

/-- The outward predicate retains the disposition of the actual selected
operation instance, rather than a mode inferred independently at its consumer. -/
theorem MayAwait.operation_ready {program : Kernel.Program} {function : Function} {state : State}
    {boundary : InvocationBoundary} {context : Execution.Context} {id : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace} {operation : OperationDefinition} {signature : Signature}
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature) :
    ∃ disposition, OperationDisposition.Matches operation disposition ∧
      boundary.OperationReady program state payload disposition := by
  obtain ⟨_,_,_,_,actual,_,task,actualInstance,_,_,_,permission⟩ := awaiting
  obtain ⟨rfl,rfl,rfl,rfl⟩ := Task.perform.inj (task.symm.trans pending)
  have same := actualInstance.definition_eq selected
  subst actual
  exact permission

theorem MayAwait.outward {program : Kernel.Program} {function : Function} {state : State}
    {boundary : InvocationBoundary} {context : Execution.Context} {id : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace}
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload) :
    ¬ boundary.InternalOperation program state id arguments payload := by
  obtain ⟨_,_,_,_,_,_,task,_,_,_,outside,_⟩ := awaiting
  obtain ⟨rfl,rfl,rfl,rfl⟩ := Task.perform.inj (task.symm.trans pending)
  exact outside

theorem MayAwait.foreign_free {program : Kernel.Program} {function : Function} {state : State}
    {boundary : InvocationBoundary} (awaiting : MayAwait program function state boundary) :
    ∃ inner, state.frames = inner ++ boundary.ambient ∧ ∀ frame ∈ inner, frame.ForeignFree := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,disposition,_,ready⟩ := awaiting
  exact ready.foreign_free

/-- Admission produces the actual ordered payload-preparation outcome for
the clause home, including a resource-exhausted prefix. -/
theorem MayAwait.prepare {program : Kernel.Program} {function : Function} {state : State}
    {boundary : InvocationBoundary} {context clause : Execution.Context} {id : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace} {operation : OperationDefinition}
    {signature : Signature} {disposition : OperationDisposition} {withRegion : World}
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature)
    (matched : OperationDisposition.Matches operation disposition)
    (home : OperationPayloadContext state clause withRegion) (valid : withRegion.WellFormed) :
    ∃ kept moved outcome,
      ProtectsAttemptFor program clause (payload.map ResolvedPlace.address) withRegion payload kept moved outcome ∧
      moved.WellFormed ∧
      (outcome = .complete → ∃ inner roots, state.frames = inner ++ boundary.ambient ∧
        AbandonedRoots moved inner (kept.map Address.root) roots ∧
        OperationDisposition.Permits program moved roots inner disposition) := by
  obtain ⟨actual,actualMode,ready⟩ := awaiting.operation_ready pending selected
  have same := actualMode.functional matched
  subst actual
  exact ready.prepare home valid

/-- For any actual outward route and actual payload preparation, the caller's
share supplies precisely the remaining permission of the real terminal or
resumptive rule. The callee's permission is obtained from admission. -/
theorem MayAwait.caller_permission {program : Kernel.Program} {function : Function} {state : State}
    {boundary : InvocationBoundary} {context clause : Execution.Context} {id : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace} {operation : OperationDefinition}
    {signature : Signature} {disposition : OperationDisposition} {kept : List Address} {moved : World}
    {abandoned outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {all : List Identity}
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selectedOperation : OperationInstance program id arguments operation signature)
    (matched : OperationDisposition.Matches operation disposition)
    (route : Routes program state id arguments payload abandoned handler owns arm outer)
    (prepared : PreparedOperationPayload program state payload clause kept moved)
    (selectedRoots : DelimitedRoots moved handler abandoned (kept.map Address.root) all) :
    ∃ caller, boundary.ambient = caller ++ .handler handler owns :: outer ∧
      ∀ callerRoots, DelimitedRoots moved handler caller (kept.map Address.root) callerRoots →
        (OperationDisposition.Permits program moved callerRoots caller disposition ↔
          OperationDisposition.Permits program moved all abandoned disposition) := by
  obtain ⟨actual,actualMode,ready⟩ := awaiting.operation_ready pending selectedOperation
  have same := actualMode.functional matched
  subst actual
  exact ready.caller_permission (awaiting.outward pending) route prepared selectedRoots

/-- An outward label retains an actual destination and positive payload request,
with permission on its callee-owned post-payload remainder. The caller supplies
its own residual cleanup share when consuming this request. Missing routing or
impossible protection is not permission for an invalid destination. -/
def MayTransfer (program : Kernel.Program) (state : State)
    (boundary : InvocationBoundary) : Prop :=
  ∃ brand result, boundary.OutwardLabel state brand result ∧ boundary.LabelReady program state brand result

theorem MayTransfer.isolated_false {program : Kernel.Program} {state : State} :
    ¬ MayTransfer program state .isolated := by
  rintro ⟨brand,argument,outward,ready⟩
  obtain ⟨abandoned,context,region,type,outer,_,_,route,_⟩ := ready.preflight
  exact outward.2 ⟨abandoned,context,region,type,outer,by simpa only [InvocationBoundary.ambient,List.append_nil] using route⟩

theorem MayTransfer.foreign_free {program : Kernel.Program} {state : State} {boundary : InvocationBoundary}
    (transfer : MayTransfer program state boundary) :
    ∃ callee, state.frames = callee ++ boundary.ambient ∧ ∀ frame ∈ callee, frame.ForeignFree := by
  obtain ⟨_,_,_,ready⟩ := transfer
  exact ready.foreign_free

theorem MayTransfer.execute {program : Kernel.Program} {state : State} {boundary : InvocationBoundary}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program state.world) (transfer : MayTransfer program state boundary)
    (caller : ∀ brand argument, boundary.OutwardLabel state brand argument →
      boundary.LabelCallerPermission program state brand argument) :
    ∃ after event, ControlStep program state event after ∧ Typing.WorldTyped program after.world ∧
      (event = none ∨ event = some (.fatal .resource) ∧ after = { state with task := .fatal .resource }) := by
  obtain ⟨brand,argument,outward,ready⟩ := transfer
  obtain ⟨context,pending⟩ := outward.1
  exact ready.execute valid inventory typed outward.2 pending (caller brand argument outward)

def StateProgress (program : Kernel.Program) (host : Foreign.Model) (function : Function) (state : State)
    (boundary : InvocationBoundary := .isolated) : Prop :=
  (∃ result, boundary.Normal state result) ∨ (∃ reason, state.task = .fatal reason) ∨
    MayAwait program function state boundary ∨ MayTransfer program state boundary ∨
    ∃ event after, InvocationStep program host boundary state event after

/-- A caller handoff cannot be mistaken for a valid return with the wrong
saved context. Progress admission has no continuation step across the boundary. -/
theorem StateProgress.handoff_normal {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {state : State} {boundary : InvocationBoundary}
    (progress : StateProgress program host function state boundary)
    (handoff : boundary.Handoff state) : ∃ result, boundary.Normal state result := by
  cases boundary with
  | isolated => obtain ⟨context,result,stopped⟩ := handoff; exact ⟨result,context,stopped⟩
  | caller returnTo ambient =>
    obtain ⟨context,result,task,frames⟩ := handoff
    rcases progress with normal | ⟨reason,fatal⟩ | awaiting | transfer | ⟨event,after,step⟩
    · exact normal
    · simp only [task,reduceCtorEq] at fatal
    · obtain ⟨_,_,_,_,_,_,pending,_⟩ := awaiting
      simp only [task,reduceCtorEq] at pending
    · obtain ⟨_,_,⟨⟨_,pending⟩,_⟩,_⟩ := transfer
      simp only [task,reduceCtorEq] at pending
    · exact False.elim (step.not_handoff ⟨context,result,task,frames⟩)

/-- The remaining path-sensitive obligations. Storage typing is not a second
admission premise: `SemanticPreservation` derives it for every execution from
well-formed declarations, the body inventory and the host's actual laws. -/
def ResourceAdmissionAt (program : Kernel.Program) (function : Function) (access : Access) : Prop :=
  ∀ host inputs boundary start trace finish,
    Foreign.Model.Lawful program host → InvocationStart program host function inputs boundary start →
    (∀ input ∈ inputs, (∃ index, input.origin = .capture index) → input.access = access) →
    InvocationRun program host boundary start trace finish →
    StateProgress program host function finish boundary ∧
    (∀ result value, boundary.Normal finish result → finish.world.Stores result value →
      Subtype program.declarations ⟨[],[],0,default,false,{}⟩ value.type function.signature.result) ∧
    (∀ result, boundary.Normal finish result →
      ∀ id root, finish.world.roots.get id = some root → root.live = true →
        (∃ old, start.world.roots.get id = some old) ∨ result.root = id ∨
        (∃ domain, root.home = .allocation domain ∨ root.home = .external domain))

def ResourceAdmission (program : Kernel.Program) (function : Function) : Prop := ResourceAdmissionAt program function .owned

def OriginalInputSurvives (before after : World) (input : InvocationInput) : Prop :=
  ∀ value, before.Stores input.storage value →
    ∃ current, after.Stores input.storage current ∧ current.owner = value.owner ∧ current.type = value.type ∧ current.Initialized

def ReceiverAccess (receiver : Term) (type : Term) (access : Access) : Prop :=
  (receiver = type ∧ access = .owned) ∨
  (∃ region, receiver = .reference .shared region type ∧ access = .shared) ∨
  (∃ region, receiver = .reference .unique region type ∧ access = .unique)

def RelationHolds (program : Kernel.Program) (function : Function) (relation : InvocationRelation) : Prop :=
  relation.arguments = function.signature.parameters ∧ relation.result = function.signature.result ∧
  relation.effects = function.signature.effects ∧ relation.unsafeAllowed = function.signature.unsafeAllowed ∧
  ∃ arguments access,
    ReceiverAccess relation.receiver (.callable function.declaration arguments) access ∧
    (∀ host observation, Foreign.Model.Lawful program host → Observes program host function observation →
      (∀ input ∈ observation.input, (∃ index, input.origin = .capture index) → input.access = access) →
      (∀ result, observation.outcome = .normal result →
        access ≠ .owned → relation.after = relation.access ∧
          ∀ input ∈ observation.input, (∃ index, input.origin = .capture index) → OriginalInputSurvives observation.before observation.after input)) ∧
    ResourceAdmissionAt program function access

def CheckedInterfaces (program : Kernel.Program) : Prop :=
  ∀ declaration, program.declarations.function declaration.header.id = some declaration →
    ∀ arguments function substitution relation,
      Instance program declaration.header.id arguments function → Instantiates declaration.signature.generics arguments substitution →
      relation ∈ declaration.invocations →
      RelationHolds program function
        ⟨relation.receiver.substitute substitution,relation.access.substitute substitution,
          relation.arguments.map (Term.substitute substitution),relation.result.substitute substitution,
          relation.effects.substitute substitution,relation.after.substitute substitution,relation.unsafeAllowed⟩

def PlainBoundary (world : World) (values : List Address) : Prop :=
  ∀ id available, world.availability.get id = some available → available.active = true →
    ∀ address ∈ values, ∀ value path resident, world.Stores address value → ResidentAt value path resident → resident.head ≠ .available id

def ClosedResult (observation : Observation) : Prop :=
  ∀ result, observation.outcome = .normal result → PlainBoundary observation.after [result] ∧
    ∀ id available, observation.after.availability.get id = some available → available.active = true →
      ∃ original, observation.before.availability.get id = some original ∧ original = available

def DropTraceSafe (before : World) (inputs : List InvocationInput) (events : List Event) : Prop :=
    (∀ event ∈ events,
      (∀ brand, event ≠ .leave brand) ∧ (∀ id, event ≠ .suspend id) ∧
      (∀ id last, event ≠ .replay id last)) ∧
    (∀ input ∈ inputs, ∀ value id loan, before.Stores input.storage value → value.head = .reference id →
      before.loans.get id = some loan →
      ∀ source destination, Event.move source destination ∈ events → ¬ source.Overlaps loan.referent)

/-- Normal Drop completion ends the original loan and restores initialized
borrowing storage. Source reassignment may install a new Self owner. This
does not grant an arbitrary ancestor authority: ordinary release can also end
an unreferenced parent, while retained caller authority is a frame obligation. -/
def DropBorrowReturned (self : Term) (after : World) (id : Identity) (original : Loan) : Prop :=
  after.loans.get id = some { original with live := false } ∧
    ∃ current, after.Stores original.referent current ∧ current.type = self ∧ current.Initialized

/-- Destructor restrictions are safety properties of every actual execution
prefix, including a hook that subsequently diverges and has no final outcome. -/
def DropContract (program : Kernel.Program) (self region : Term) (function : Function) : Prop :=
  DropFunction self region function ∧
  (∀ host inputs boundary start events finish, Foreign.Model.Lawful program host →
    InvocationStart program host function inputs boundary start → InvocationRun program host boundary start events finish →
    DropTraceSafe start.world inputs events ∧
      ∀ operation arguments payload, ¬ boundary.OutwardOperation program finish operation arguments payload) ∧
  (∀ host observation, Foreign.Model.Lawful program host → Observes program host function observation →
    ∀ result, observation.outcome = .normal result →
    ∀ input ∈ observation.input, ∀ value id original, observation.before.Stores input.storage value →
      value.head = .reference id → observation.before.loans.get id = some original →
      DropBorrowReturned self observation.after id original) ∧
  ResourceAdmission program function

theorem exact_interface_is_derived (program : Kernel.Program) (function : Function) :
    Derived program function (ExactInterface program function) := by
  constructor
  · intro host observation lawful observed
    exact ⟨host,lawful,observed⟩
  · constructor
    · intro host inputs states events lawful infinite
      exact ⟨host,lawful,infinite⟩
    · intro host observation lawful lifecycle
      exact ⟨host,lawful,lifecycle⟩

theorem unknown_is_not_normal {program : Kernel.Program} {boundary : InvocationBoundary}
    {state : State} : ¬ AtOutcome program boundary state .unknown := by
  intro impossible
  exact impossible

end Glorious.Language.Contracts
