import GloriousLanguage.Origins
import GloriousLanguage.ABI

/-! The language contract and the future compiler obligation. This module
does not provide a compiler and does not import the earlier compiler draft.
All executable clauses use `Execution.Step`; all source clauses use the
AST-indexed grammar and elaboration relation. -/
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

def BodyInventory (program : Kernel.Program) : Prop :=
  (program.functions.map (·.declaration)).Nodup ∧
  (∀ function ∈ program.functions, ∃ declaration, program.declarations.function function.declaration = some declaration ∧
    function.signature = declaration.signature ∧ function.parameters.map (·.id) = declaration.parameters ∧
    function.captures.map (·.type) = declaration.captures) ∧
  (∀ declaration anchor, program.declarations.function declaration.header.id = some declaration → declaration.origin = .source anchor →
    ∃ function ∈ program.functions, function.declaration = declaration.header.id)

def FunctionsAdmitted (program : Kernel.Program) : Prop :=
  ∀ id arguments function, Instance program id arguments function →
    Typing.FunctionType program function ∧ Contracts.ResourceAdmission program function ∧
    (∀ host observation, Foreign.Model.Lawful program host → Contracts.Observes program host function observation → Contracts.ClosedResult observation)

def DropsAdmitted (program : Kernel.Program) : Prop :=
  ∀ data hook arguments function,
    program.declarations.data data.header.id = some data → data.dropHook = some hook → Instance program hook arguments function →
    Contracts.DropContract program function ∧
    (∀ principal typeArguments, PrincipalOf program.declarations (.nominal data.header.id typeArguments) principal → principal.MayDiscard)

structure WellFormed (program : Kernel.Program) : Prop where
  declarations : ProgramWellFormed program.declarations
  source : Elaboration.SourceProgram program
  roles : SealedRoles program
  closed : ClosedInterfaces program
  inventory : BodyInventory program
  functions : FunctionsAdmitted program
  interfaces : Contracts.CheckedInterfaces program
  drops : DropsAdmitted program

inductive PublicValue where
  | unit
  | scalar (value : ScalarValue)
  | aggregate (type : Term) (variant : Option DeclId) (fields : List PublicValue)
  | reference (mode : Mutability) (address : Address)
  | pointer (address : Nat)
  | callable (declaration : DeclId) (arguments : List Term)
  deriving Repr, Inhabited

mutual
  inductive Reveals (world : World) : Value → PublicValue → Prop where
    | unit {owner} : Reveals world (.resident owner .unit .unit true []) .unit
    | scalar {owner scalar} : Reveals world (.resident owner (.scalar scalar.type) (.scalar scalar) true []) (.scalar scalar)
    | aggregate {owner type head fields values variant} :
        (head = .tuple ∧ variant = none ∨ head = .array ∧ variant = none ∨ ∃ id, head = .constructor id ∧ variant = some id) →
        RevealsFields world fields values → Reveals world (.resident owner type head true fields) (.aggregate type variant values)
    | reference {owner type id loan} : world.loans.get id = some loan → loan.live = true →
        Reveals world (.resident owner type (.reference id) true []) (.reference loan.mode loan.referent)
    | pointer {owner type pointer} : Reveals world (.resident owner type (.pointer pointer) true []) (.pointer pointer.address)
    | callable {owner type id arguments fields} : Reveals world (.resident owner type (.callable id arguments) true fields) (.callable id arguments)

  inductive RevealsFields (world : World) : List (Option Value) → List PublicValue → Prop where
    | nil : RevealsFields world [] []
    | cons {value values public publics} : Reveals world value public → RevealsFields world values publics →
        RevealsFields world (some value :: values) (public :: publics)
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
  (∃ address value public, state.task = .stopped address ∧ state.world.Stores address value ∧ Reveals state.world value public ∧ result = .returned public) ∨
  (∃ reason, state.task = .fatal reason ∧ result = .fatal reason) ∨
  (∃ context id arguments payload residents public,
    state.task = .perform context id arguments payload ∧ Contracts.MayAwait program function state ∧
    ListRel (World.Stores state.world) payload residents ∧ ListRel (Reveals state.world) residents public ∧ result = .outward id arguments public)

def Semantics (program : Kernel.Program) (host : Foreign.Model) (function : Function) (inputs : List InvocationInput) :
    TransitionSystem PublicEvent Result where
  State := State
  initial := Contracts.InitialInvocation program function inputs
  step before event after := ∃ internal, Execution.Step program host before internal after ∧ event = internal.bind publicEvent
  final := Finished program function
  invalid state := ¬ Typing.WorldTyped program state.world

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
    Preserves (Semantics (implementation.source artifact) host function inputs) (implementation.vm artifact host function inputs).semantics ∧
    Preserves (Semantics (implementation.source artifact) host function inputs) (implementation.native artifact host function inputs).semantics

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
    ∃ vmSites : List (ABI.TailEvidence (implementation.vm artifact host function inputs)),
      ∃ nativeSites : List (ABI.TailEvidence (implementation.native artifact host function inputs)),
        vmSites.map (·.site) = nativeSites.map (·.site)
  labelErasure : ∀ budget input artifact host function inputs,
    implementation.compile budget input = .ok artifact →
      Nonempty (ABI.LabelFusion (implementation.vm artifact host function inputs)) ∧
      Nonempty (ABI.LabelFusion (implementation.native artifact host function inputs))

theorem always_rejecting_not_complete {implementation : Implementation} {input : Language.Input}
    (valid : ValidInput input)
    (rejects : ∀ budget artifact, implementation.compile budget input ≠ .ok artifact) :
    ¬ CompleteWithinDeclaredLimits implementation := by
  intro complete
  obtain ⟨budget,artifact,accepted⟩ := complete input valid
  exact rejects budget artifact accepted

end Glorious.Language.Specification
