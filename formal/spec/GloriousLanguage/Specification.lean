import GloriousLanguage.Origins
import GloriousLanguage.ABI
import GloriousLanguage.ABISiteAdmission

/-! The language contract and the future compiler obligation. This module
does not provide a compiler and does not import the earlier compiler draft.
All executable clauses use `Execution.Step`; all source clauses use the
AST-indexed grammar and elaboration relation. -/
universe u

namespace Glorious.Language.Specification

open Kernel Execution

def SealedRoles (program : Kernel.Program) : Prop :=
  (program.declarations.input.manifest.sealedRelations.map Prod.fst).Nodup ∧
  (∀ trait, program.declarations.trait trait.header.id = some trait →
    (trait.relation = .ordinary ∧ (∀ relation, (trait.header.id,relation) ∉ program.declarations.input.manifest.sealedRelations)) ∨
      (trait.header.id,trait.relation) ∈ program.declarations.input.manifest.sealedRelations) ∧
  (∀ implementation, Definition.implementation implementation ∈ program.declarations.declarations →
    ∀ trait, program.declarations.trait implementation.trait = some trait →
      trait.relation ∈ [.ordinary,.use,.drop])

def ClosedInterfaces (program : Kernel.Program) : Prop :=
  ∀ definition ∈ program.declarations.declarations,
    match definition with
    | .function function =>
      (∀ term ∈ function.signature.parameters ++ [function.signature.result,function.signature.effects],
        ∀ id kind level, ¬ Occurs (.variable id kind level) term) ∧
      (∀ relation ∈ function.invocations, ∀ term ∈ relation.arguments ++
        [relation.receiver,relation.access,relation.result,relation.effects,relation.after],
        ∀ id kind level, ¬ Occurs (.variable id kind level) term)
    | .data data => ∀ variant ∈ data.variants, ∀ field ∈ variant.fields, ∀ id kind level, ¬ Occurs (.variable id kind level) field.type
    | .alias alias => ∀ id kind level, ¬ Occurs (.variable id kind level) alias.value
    | .constant constant => Closed constant.value ∨ constant.generics ≠ []
    | _ => True

def FunctionsAdmitted (program : Kernel.Program) : Prop :=
  ∀ id arguments function, Instance program id arguments function →
    Typing.FunctionType program function ∧ Contracts.ResourceAdmission program function ∧
    (∀ host observation, Foreign.Model.Lawful program host → Contracts.Observes program host function observation → Contracts.ClosedResult observation)

structure DropsAdmitted (program : Kernel.Program) : Prop where
  applications : DropApplications program.declarations
  contracts : ∀ self region hook function, DropInstance program self region hook function →
    Contracts.DropContract program self region function

structure WellFormed (program : Kernel.Program) : Prop where
  declarations : ProgramWellFormed program.declarations
  source : Elaboration.SourceProgram program
  roles : SealedRoles program
  closed : ClosedInterfaces program
  inventory : BodyInventory program
  functions : FunctionsAdmitted program
  interfaces : Contracts.CheckedInterfaces program
  drops : DropsAdmitted program

/-- Logical source-value observations, not a physical ABI. Captured residents
remain part of a returned callable. Control/context identities record their
logical value without granting an address or permission to escape a lifetime. -/
inductive PublicValue where
  | unit
  | scalar (value : ScalarValue)
  | aggregate (type : Term) (variant : Option DeclId) (fields : List PublicValue)
  | reference (mode : Mutability) (address : Address)
  | pointer (address : Nat)
  | callable (declaration : DeclId) (arguments : List Term) (captures : List PublicValue)
  | label (brand : Identity)
  | continuation (identity : Identity)
  | available (identity : Identity)
  | bindings (pack : BindingPack) (fields : List PublicValue)
  deriving Repr, Inhabited

mutual
  /-- The public observation of a live resident. Erased resource obligations are
  internal ownership state, never part of the public value, so every constructor
  carries the actual `resources` of the resident instead of pinning them empty. -/
  inductive Reveals (world : World) : Value → PublicValue → Prop where
    | unit {owner resources} : Reveals world (.resident owner .unit .unit true [] resources) .unit
    | scalar {owner scalar resources} : Reveals world (.resident owner (.scalar scalar.type) (.scalar scalar) true [] resources) (.scalar scalar)
    | aggregate {owner type head fields values variant resources} :
        (head = .tuple ∧ variant = none ∨ head = .array ∧ variant = none ∨ ∃ id, head = .constructor id ∧ variant = some id) →
        RevealsFields world fields values → Reveals world (.resident owner type head true fields resources) (.aggregate type variant values)
    | reference {owner type id loan resources} : world.loans.get id = some loan → loan.live = true →
        Reveals world (.resident owner type (.reference id) true [] resources) (.reference loan.mode loan.referent)
    | pointer {owner type pointer resources} : Reveals world (.resident owner type (.pointer pointer) true [] resources) (.pointer pointer.address)
    | callable {owner type id arguments fields captures resources} : RevealsFields world fields captures →
        Reveals world (.resident owner type (.callable id arguments) true fields resources) (.callable id arguments captures)
    | operation {owner type id arguments resources} :
        Reveals world (.resident owner type (.operation id arguments) true [] resources) (.callable id arguments [])
    | label {owner type brand resources} : Reveals world (.resident owner type (.label brand) true [] resources) (.label brand)
    | continuation {owner type id resources} : Reveals world (.resident owner type (.continuation id) true [] resources) (.continuation id)
    | available {owner type id resources} : Reveals world (.resident owner type (.available id) true [] resources) (.available id)
    | bindings {owner type pack fields values resources} : RevealsFields world fields values →
        Reveals world (.resident owner type (.bindings pack) true fields resources) (.bindings pack values)

  inductive RevealsFields (world : World) : List (Option Value) → List PublicValue → Prop where
    | nil : RevealsFields world [] []
    | cons {value values publicScope publics} : Reveals world value publicScope → RevealsFields world values publics →
        RevealsFields world (some value :: values) (publicScope :: publics)
end

inductive PublicEvent where
  | host (symbol : String) (input output : List Nat)
  | effect (operation : DeclId) (arguments : List Term)
  | fault (reason : Fatal)
  deriving Repr, Inhabited

def publicEvent : Event → Option PublicEvent
  | .host symbol input output => some (.host symbol input output)
  | .perform operation arguments => some (.effect operation arguments)
  | .fatal reason => some (.fault reason)
  | _ => none

inductive Result where
  | returned (value : PublicValue)
  | outward (operation : DeclId) (arguments : List Term) (payload : List PublicValue)
  | fatal (reason : Fatal)
  deriving Repr, Inhabited

def Finished (program : Kernel.Program) (function : Function) (state : State) (result : Result) : Prop :=
  (∃ context address value publicScope, state.task = .stopped context address ∧ state.world.Stores address value ∧ Reveals state.world value publicScope ∧ result = .returned publicScope) ∨
  (∃ reason, state.task = .fatal reason ∧ result = .fatal reason) ∨
  (∃ context id arguments payload residents publicScope,
    state.task = .perform context id arguments payload ∧ Contracts.MayAwait program function state ∧
    ListRel (fun source value => state.world.Stores source.address value) payload residents ∧
    ListRel (Reveals state.world) residents publicScope ∧ result = .outward id arguments publicScope)

/-- The public executable semantics. `invalid` denies every state outside the
intended well-formed domain: storage typing always, and complete control
provenance up to the resource-exhaustion terminal, which is a real machine
endpoint rather than an ill-formed state. This is what makes the public safety
chain consume `State.ControlWellFormed`, through `reachable_control`. -/
def Semantics (program : Kernel.Program) (host : Foreign.Model) (function : Function) (inputs : List InvocationInput) :
    TransitionSystem PublicEvent Result where
  State := State
  initial := Contracts.InitialInvocation program host function inputs
  step before event after := ∃ internal, Execution.Step program host before internal after ∧ event = internal.bind publicEvent
  final := Finished program function
  invalid state := ¬ (Typing.WorldTyped program state.world ∧
    (state.ControlWellFormed ∨ state.task = .fatal .resource))
theorem rawStepsToInvocation (program : Kernel.Program) (host : Foreign.Model)
    (function : Function) (inputs : List InvocationInput)
    {start finish : State} {trace : List Execution.Event}
    (path : (ABI.SourceSemantics program host).Steps start trace finish) :
    (Semantics program host function inputs).Steps start (trace.filterMap publicEvent) finish := by
  refine TransitionSystem.Steps.rec (system := ABI.SourceSemantics program host)
    (motive := fun (start : State) (trace : List Execution.Event) (finish : State) _ =>
      (Semantics program host function inputs).Steps start (trace.filterMap publicEvent) finish)
    ?_ ?_ ?_ path
  · exact .refl
  · intro start middle finish trace step rest ih
    have mapped : (Semantics program host function inputs).step start none middle := by
      refine ⟨none,?_,rfl⟩
      simpa [ABI.SourceSemantics] using step
    exact .silent mapped ih
  · intro start middle finish event trace step rest ih
    change Execution.Step program host start (some event) middle at step
    cases observed : publicEvent event with
    | none =>
        have mapped : (Semantics program host function inputs).step start none middle :=
          ⟨some event,step,by simp [observed]⟩
        apply TransitionSystem.Steps.silent mapped
        simpa [observed] using ih
    | some publicValue =>
        have mapped : (Semantics program host function inputs).step start (some publicValue) middle :=
          ⟨some event,step,by simp [observed]⟩
        simpa [observed] using (TransitionSystem.Steps.visible mapped ih)

structure EngineInvocationBoundary (engine : ABI.Engine PublicEvent Result)
    (source : TransitionSystem PublicEvent Result) (project : source.State → State) : Prop where
  initialForward : ∀ sourceStart, source.initial sourceStart →
    ∃ targetStart, engine.semantics.initial targetStart ∧ engine.sourceState targetStart (project sourceStart)
  initialBackward : ∀ targetStart, engine.semantics.initial targetStart →
    ∃ sourceStart, source.initial sourceStart ∧ engine.sourceState targetStart (project sourceStart)
  finalForward : ∀ {sourceEnd targetStart result},
    engine.sourceState targetStart (project sourceEnd) → source.final sourceEnd result →
    ∃ targetEnd, engine.semantics.Steps targetStart [] targetEnd ∧
      engine.sourceState targetEnd (project sourceEnd) ∧ engine.semantics.final targetEnd result
  finalBackward : ∀ {sourceStart targetEnd result},
    engine.sourceState targetEnd (project sourceStart) → engine.semantics.final targetEnd result →
    ∃ sourceEnd, source.Steps sourceStart [] sourceEnd ∧
      engine.sourceState targetEnd (project sourceEnd) ∧ source.final sourceEnd result
  invalidReflection : ∀ {sourceState targetState},
    engine.sourceState targetState (project sourceState) →
    engine.semantics.invalid targetState → source.invalid sourceState

noncomputable def engineInvocationRefinement (engine : ABI.Engine PublicEvent Result)
    (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (inputs : List InvocationInput)
    (programEq : engine.program = program) (hostEq : engine.host = host)
    (observation : ∀ event, engine.observe event = publicEvent event)
    (boundary : EngineInvocationBoundary engine
      (Semantics program host function inputs) (fun state => state)) :
    WeakRefinement.{u} (Semantics program host function inputs) engine.semantics
      (fun sourceState targetState => engine.sourceState targetState sourceState) := by
  refine {
    Rank := engine.Rank
    decrease := engine.rankDecrease
    wellFounded := engine.rankWellFounded
    rank := fun sourceState targetState => engine.stutterRank targetState sourceState
    initialForward := boundary.initialForward
    initialBackward := boundary.initialBackward
    finalForward := boundary.finalForward
    finalBackward := boundary.finalBackward
    invalidReflection := boundary.invalidReflection
    forwardStep := ?_
    backwardStep := ?_
  }
  · intro sourceStart event sourceNext targetStart related sourceStep
    rcases sourceStep with ⟨internal,rawStep,eventEq⟩
    rw [← programEq,← hostEq] at rawStep
    have mappedEvent : internal.bind engine.observe = event := by
      calc
        internal.bind engine.observe = internal.bind publicEvent := by
          cases internal with
          | none => rfl
          | some raw => simp [observation raw]
        _ = event := eventEq.symm
    rcases engine.realizes sourceStart internal sourceNext rawStep targetStart related with
      matched | stutter
    · obtain ⟨targetNext,path,nextRelated⟩ := matched
      left
      exact ⟨targetNext,by simpa [mappedEvent] using path,nextRelated⟩
    · right
      have eventNone : event = none := by rw [← mappedEvent]; exact stutter.1
      exact ⟨eventNone,stutter.2.1,stutter.2.2⟩
  · intro sourceStart targetStart event targetNext related targetStep
    rcases engine.reflects targetStart event targetNext targetStep sourceStart related with
      matched | stutter
    · obtain ⟨sourceNext,trace,rawPath,traceObservation,nextRelated⟩ := matched
      have rawPath' := rawPath
      rw [programEq,hostEq] at rawPath'
      rcases rawPath' with ⟨rawEvent,middle,suffix,rawStep,rawRest,traceEq⟩
      have mappedStep : (Semantics program host function inputs).step sourceStart
          (rawEvent.bind publicEvent) middle := ⟨rawEvent,rawStep,rfl⟩
      have mappedPath : (Semantics program host function inputs).PositiveSteps sourceStart
          (trace.filterMap publicEvent) sourceNext := by
        refine ⟨rawEvent.bind publicEvent,middle,suffix.filterMap publicEvent,
          mappedStep,rawStepsToInvocation program host function inputs rawRest,?_⟩
        rw [traceEq, List.filterMap_append]
        cases rawEvent with
        | none => rfl
        | some raw => cases publicEvent raw <;> rfl
      have mappedObservation : trace.filterMap publicEvent = event.toList := by
        have equalMaps : trace.filterMap engine.observe = trace.filterMap publicEvent := by
          rw [funext observation]
        exact equalMaps.symm.trans traceObservation
      left
      exact ⟨sourceNext,by simpa [mappedObservation] using mappedPath,nextRelated⟩
    · right
      exact ⟨stutter.1,stutter.2.1,stutter.2.2⟩

inductive Rejection where
  | source (reason : Failure) (span : Option Span)
  | limit (kind : Limit)
  | target (reason : Failure)
  deriving Repr, Inhabited

def ValidInput (input : Language.Input) : Prop :=
  ∃ program : Kernel.Program, program.declarations.input = input ∧ WellFormed program

structure Implementation where
  Artifact : Type
  compile : Nat → Language.Input → Except Rejection Artifact
  source : Artifact → Kernel.Program
  vm : Artifact → Foreign.Model → Function → List InvocationInput → ABI.Engine PublicEvent Result
  native : Artifact → Foreign.Model → Function → List InvocationInput → ABI.Engine PublicEvent Result

def SourceCorrect (implementation : Implementation) : Prop :=
  ∀ budget input artifact, implementation.compile budget input = .ok artifact →
    (implementation.source artifact).declarations.input = input ∧ WellFormed (implementation.source artifact)

def BehaviorCorrect (implementation : Implementation) : Prop :=
  ∀ budget input artifact host id arguments function inputs,
    implementation.compile budget input = .ok artifact →
    Instance (implementation.source artifact) id arguments function → Foreign.Model.Lawful (implementation.source artifact) host →
    ((implementation.vm artifact host function inputs).program = implementation.source artifact ∧
      (implementation.vm artifact host function inputs).host = host) ∧
    (∀ event, (implementation.vm artifact host function inputs).observe event = publicEvent event) ∧
      Nonempty (EngineInvocationBoundary (implementation.vm artifact host function inputs)
        (Semantics (implementation.source artifact) host function inputs) (fun state => state)) ∧
    ((implementation.native artifact host function inputs).program = implementation.source artifact ∧
      (implementation.native artifact host function inputs).host = host) ∧
    (∀ event, (implementation.native artifact host function inputs).observe event = publicEvent event) ∧
      Nonempty (EngineInvocationBoundary (implementation.native artifact host function inputs)
        (Semantics (implementation.source artifact) host function inputs) (fun state => state))
theorem BehaviorCorrect.preserves {implementation : Implementation}
    (behavior : BehaviorCorrect implementation)
    {budget : Nat} {input : Language.Input} {artifact : implementation.Artifact}
    {host : Foreign.Model} {id : DeclId} {arguments : List Term}
    {function : Function} {inputs : List InvocationInput}
    (compiled : implementation.compile budget input = .ok artifact)
    (instanceProof : Instance (implementation.source artifact) id arguments function)
    (lawful : Foreign.Model.Lawful (implementation.source artifact) host) :
    Preserves (Semantics (implementation.source artifact) host function inputs)
      (implementation.vm artifact host function inputs).semantics ∧
    Preserves (Semantics (implementation.source artifact) host function inputs)
      (implementation.native artifact host function inputs).semantics := by
  have contract := behavior budget input artifact host id arguments function inputs compiled instanceProof lawful
  rcases contract.2.2.1 with ⟨vmBoundary⟩
  rcases contract.2.2.2.2.2 with ⟨nativeBoundary⟩
  let vmRefinement := engineInvocationRefinement
    (implementation.vm artifact host function inputs) (implementation.source artifact) host function inputs
    contract.1.1 contract.1.2 contract.2.1 vmBoundary
  let nativeRefinement := engineInvocationRefinement
    (implementation.native artifact host function inputs) (implementation.source artifact) host function inputs
    contract.2.2.2.1.1 contract.2.2.2.1.2 contract.2.2.2.2.1 nativeBoundary
  exact ⟨vmRefinement.preserves,nativeRefinement.preserves⟩
def CompleteWithinDeclaredLimits (implementation : Implementation) : Prop :=
  ∀ input, ValidInput input → ∃ budget artifact, implementation.compile budget input = .ok artifact

structure CompilerContract (implementation : Implementation) : Prop where
  accepted : SourceCorrect implementation
  behavior : BehaviorCorrect implementation
  acceptance : CompleteWithinDeclaredLimits implementation
  shared : ∀ budget input artifact host id arguments function inputs,
    implementation.compile budget input = .ok artifact → Instance (implementation.source artifact) id arguments function →
    Foreign.Model.Lawful (implementation.source artifact) host →
    ∃ runtime, ABI.SharedABI (implementation.source artifact) runtime
      (implementation.vm artifact host function inputs) (implementation.native artifact host function inputs)
  mandatoryTail : ∀ budget input artifact host function inputs,
    implementation.compile budget input = .ok artifact →
    (implementation.vm artifact host function inputs).program = implementation.source artifact ∧
    (implementation.native artifact host function inputs).program = implementation.source artifact ∧
    ∃ vmSites : List (ABI.TailEvidence (implementation.vm artifact host function inputs)),
      ∃ nativeSites : List (ABI.TailEvidence (implementation.native artifact host function inputs)),
        vmSites.map (·.site) = Kernel.TailSites (implementation.source artifact) ∧
        nativeSites.map (·.site) = Kernel.TailSites (implementation.source artifact)
  labelErasure : ∀ budget input artifact host function inputs,
    implementation.compile budget input = .ok artifact →
    (implementation.vm artifact host function inputs).program = implementation.source artifact ∧
    (implementation.native artifact host function inputs).program = implementation.source artifact ∧
    ∃ vmFusion : ABI.LabelFusion (implementation.vm artifact host function inputs),
      ∃ nativeFusion : ABI.LabelFusion (implementation.native artifact host function inputs),
        vmFusion.sites = Kernel.LabelSites (implementation.source artifact) ∧
        nativeFusion.sites = Kernel.LabelSites (implementation.source artifact)
theorem CompilerContract.sharedAtReachable {implementation : Implementation}
    (contract : CompilerContract implementation)
    {budget : Nat} {input : Language.Input} {artifact : implementation.Artifact}
    {host : Foreign.Model} {id : DeclId} {arguments : List Term}
    {function : Function} {inputs : List InvocationInput}
    (compiled : implementation.compile budget input = .ok artifact)
    (instanceProof : Instance (implementation.source artifact) id arguments function)
    (lawful : Foreign.Model.Lawful (implementation.source artifact) host)
    {sourceState : State}
    (reachable : (Semantics (implementation.source artifact) host function inputs).Reachable sourceState) :
    ∃ runtime vmState nativeState injection,
      (implementation.vm artifact host function inputs).semantics.Reachable vmState ∧
      (implementation.native artifact host function inputs).semantics.Reachable nativeState ∧
      (implementation.vm artifact host function inputs).sourceState vmState sourceState ∧
      (implementation.native artifact host function inputs).sourceState nativeState sourceState ∧
      ABI.Represents (implementation.source artifact) runtime sourceState.world
        ((implementation.vm artifact host function inputs).backing vmState) injection ∧
      ABI.Represents (implementation.source artifact) runtime sourceState.world
        ((implementation.native artifact host function inputs).backing nativeState) injection := by
  obtain ⟨runtime,abi⟩ := contract.shared budget input artifact host id arguments function inputs
    compiled instanceProof lawful
  have behavior := contract.behavior budget input artifact host id arguments function inputs
    compiled instanceProof lawful
  rcases behavior.2.2.1 with ⟨vmBoundary⟩
  rcases behavior.2.2.2.2.2 with ⟨nativeBoundary⟩
  let vmRefinement := engineInvocationRefinement
    (implementation.vm artifact host function inputs) (implementation.source artifact) host function inputs
    behavior.1.1 behavior.1.2 behavior.2.1 vmBoundary
  let nativeRefinement := engineInvocationRefinement
    (implementation.native artifact host function inputs) (implementation.source artifact) host function inputs
    behavior.2.2.2.1.1 behavior.2.2.2.1.2 behavior.2.2.2.2.1 nativeBoundary
  obtain ⟨vmState,vmReachable,vmRelation⟩ :=
    WeakRefinement.reachableForward vmRefinement reachable
  obtain ⟨nativeState,nativeReachable,nativeRelation⟩ :=
    WeakRefinement.reachableForward nativeRefinement reachable
  obtain ⟨injection,vmRepresentation,nativeRepresentation,_⟩ :=
    abi.2.2.2 sourceState vmState nativeState vmRelation nativeRelation
  exact ⟨runtime,vmState,nativeState,injection,vmReachable,nativeReachable,
    vmRelation,nativeRelation,vmRepresentation,nativeRepresentation⟩
theorem always_rejecting_not_complete {implementation : Implementation} {input : Language.Input}
    (valid : ValidInput input)
    (rejects : ∀ budget artifact, implementation.compile budget input ≠ .ok artifact) :
    ¬ CompleteWithinDeclaredLimits implementation := by
  intro complete
  obtain ⟨budget,artifact,accepted⟩ := complete input valid
  exact rejects budget artifact accepted

end Glorious.Language.Specification
