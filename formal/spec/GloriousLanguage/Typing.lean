import GloriousLanguage.Control

/-! Structural typing and semantic admission are separate. Typing establishes
resolved shapes and signatures; admission establishes path-sensitive resource,
lifetime and control obligations against the actual transition relation.
This is a specification, not a claimed decidable inference algorithm. -/
namespace Glorious.Language.Typing

open Kernel

structure Context where
  static : Language.Context
  locals : List Local
  labels : List (Identity × Term × Term)
  effects : Term
  environment : Option Term := none
  deriving Repr, Inhabited

def Context.bind (context : Context) (localSlot : Local) : Context :=
  { context with locals := localSlot :: context.locals.filter (fun previous => previous.id != localSlot.id) }

def FieldType (program : Language.Program) (context : Language.Context)
    (type : Term) (index : Nat) (field : Term) (visible : Bool) : Prop :=
  (∃ fields, type = .tuple fields ∧ fields[index]? = some field) ∨
  (∃ element length, type = .array element length ∧ field = element) ∨
  (∃ id arguments data variant substitution types,
    type = .nominal id arguments ∧ program.data id = some data ∧ data.isEnum = false ∧ data.variants = [variant] ∧
    Instantiates data.generics arguments substitution ∧ ListRel (Substitutes substitution) (variant.fields.map (·.type)) types ∧
    types[index]? = some field ∧
    (visible = true → ∃ definition, variant.fields[index]? = some definition ∧ Visible definition.header context.module))

inductive Projections (program : Language.Program) (context : Context) :
    Term → Bool → List Projection → Term → Bool → Prop where
  | nil {type mutable} : Projections program context type mutable [] type mutable
  | field {type mutable index rest field result writable} : FieldType program context.static type index field true →
      Projections program context field mutable rest result writable →
      Projections program context type mutable (.field index :: rest) result writable
  | index {element length mutable localSlot rest result writable} :
      (∃ binding ∈ context.locals, binding.id = localSlot ∧ binding.type = .scalar (.integer false .pointer)) →
      Projections program context element mutable rest result writable →
      Projections program context (.array element length) mutable (.index localSlot :: rest) result writable
  | dereference {mode region referent mutable rest result writable} :
      Projections program context referent (mode == .unique) rest result writable →
      Projections program context (.reference mode region referent) mutable (.dereference :: rest) result writable
  | equal {a b mutable projections result writable} : Equal program context.static a b →
      Projections program context b mutable projections result writable → Projections program context a mutable projections result writable

def PlaceType (program : Language.Program) (context : Context) (place : Place) (type : Term) (writable : Bool) : Prop :=
  ∃ localSlot, localSlot ∈ context.locals ∧ localSlot.id = place.localSlot ∧ Projections program context localSlot.type localSlot.mutable place.projections type writable

def PlacesType (program : Language.Program) (context : Context) (places : List Place) (types : List Term) : Prop :=
  ListRel (fun place type => ∃ actual writable, PlaceType program context place actual writable ∧ Subtype program context.static actual type) places types

def CallSignature (program : Language.Program) (context : Language.Context) (id : DeclId)
    (arguments : List Term) (signature : Signature) : Prop :=
  (∃ declaration substitution,
    program.function id = some declaration ∧ Instantiates declaration.signature.generics arguments substitution ∧
    ConstraintsHold program context substitution declaration.signature.constraints ∧ signature = declaration.signature.instantiate substitution) ∨
  (∃ operation substitution,
    program.operation id = some operation ∧ Instantiates operation.signature.generics arguments substitution ∧
    ConstraintsHold program context substitution operation.signature.constraints ∧ signature = operation.signature.instantiate substitution)

def InvocationEnvironment (program : Language.Program) (context : Context)
    (call : Invocation) (receiver : Term) : Prop :=
  call.environment = none ∨ ∃ selected brand region residents writable,
    call.environment = some selected ∧
    PlaceType program context selected.witness (.available brand region residents) writable ∧
    RunsInEnvironment program context.static call receiver brand region residents

inductive InvocationType (program : Language.Program) (context : Context) : Invocation → Prop where
  | function {call id arguments writable signature} : PlaceType program context call.callee (.callable id arguments) writable →
      InvocationEnvironment program context call (.callable id arguments) →
      CallSignature program context.static id arguments signature → signature = call.signature →
      PlacesType program context call.arguments signature.parameters →
      (signature.unsafeAllowed = true → context.static.unsafeAllowed = true) → RowSubset program context.static signature.effects context.effects →
      (call.receiver = .unique → writable = true) → InvocationType program context call
  | continuation {call brand argument answer effects quantity writable} :
      call.environment = none →
      PlaceType program context call.callee (.continuation brand argument answer effects quantity) writable →
      call.signature.parameters = [argument] → call.signature.result = answer → call.signature.effects = effects →
      PlacesType program context call.arguments [argument] → RowSubset program context.static effects context.effects →
      InvocationType program context call
  | label {call brand region result writable} : call.environment = none →
      PlaceType program context call.callee (.label brand region result) writable →
      PlacesType program context call.arguments [result] → call.signature.result = .bottom →
      call.signature.effects = .row [] [] → InvocationType program context call

mutual
  inductive PatternType (program : Language.Program) (context : Language.Context) : Pattern → Term → Access → List Local → Prop where
    | wildcard {type access} : PatternType program context .wildcard type access []
    | bind {localSlot type} : Equal program context localSlot.type type → PatternType program context (.bind localSlot) type .owned [localSlot]
    | borrowBind {localSlot type mode region} : localSlot.type = .reference mode region type → Kinding program context region .region →
        PatternType program context (.bind localSlot) type (if mode = .shared then .shared else .unique) [localSlot]
    | scalar {scalar access} : scalar.Valid program.input.target → (∀ width bits, scalar ≠ .floating width bits) →
        PatternType program context (.scalar scalar) (.scalar scalar.type) access []
    | unit {access} : PatternType program context .unit .unit access []
    | tuple {patterns types access bindings} : PatternsType program context patterns types access bindings →
        PatternType program context (.tuple patterns) (.tuple types) access bindings
    | array {patterns type sign width count access bindings} : count = patterns.length →
        PatternsType program context patterns (List.replicate patterns.length type) access bindings →
        PatternType program context (.array patterns) (.array type (.constant (.integer sign width count))) access bindings
    | constructor {id data variant arguments substitution types patterns access bindings} : program.Constructor id data variant →
        Visible variant.header context.module → Instantiates data.generics arguments substitution →
        ListRel (Substitutes substitution) (variant.fields.map (·.type)) types →
        PatternsType program context patterns types access bindings →
        (access = .owned → data.dropHook = none ∧
          (data.nonExhaustive = true → context.module.package = data.header.module.package) ∧ ∀ field ∈ variant.fields, Visible field.header context.module) →
        PatternType program context (.constructor id patterns) (.nominal data.header.id arguments) access bindings
    | reference {mode region type pattern access bindings} :
        PatternType program context pattern type
          (if access = .shared ∨ mode = .shared then .shared else .unique) bindings →
        PatternType program context (.reference mode pattern) (.reference mode region type) access bindings

  inductive PatternsType (program : Language.Program) (context : Language.Context) :
      List Pattern → List Term → Access → List Local → Prop where
    | nil {access} : PatternsType program context [] [] access []
    | cons {pattern patterns type types access bindings more} : PatternType program context pattern type access bindings →
        PatternsType program context patterns types access more →
        PatternsType program context (pattern :: patterns) (type :: types) access (bindings ++ more)
end

def CapturesType (program : Language.Program) (context : Context) (captures : List Capture) (expected : List Term) : Prop :=
  ListRel (fun capture type => capture.type = type ∧ ∃ source writable,
    PlaceType program context capture.place source writable ∧
    ((capture.mode = .own ∧ Equal program context.static source type) ∨
      (∃ region, type = .reference (if capture.mode = .shared then .shared else .unique) region source ∧
        capture.mode ≠ .own ∧ (capture.mode = .unique → writable = true)))) captures expected ∧
  (captures.map (·.formal)).Nodup

inductive AtomType (program : Kernel.Program) (context : Context) : Atom → Term → Prop where
  | constant {term type} : ConstantType program.declarations context.static term type → AtomType program context (.constant term) type
  | acquire {place force type writable} : PlaceType program.declarations context place type writable →
      AtomType program context (.acquire place force) type
  | borrow {place mode region type writable} : PlaceType program.declarations context place type writable →
      Addressable program.declarations context.static type →
      WellKinded program.declarations context.static region .region →
      (mode = .unique → writable = true) →
      AtomType program context (.borrow place mode region) (.reference mode region type)
  | construct {type variant fields fieldTypes head} : PlacesType program.declarations context fields fieldTypes →
      Execution.ConstructorHead program.declarations type variant fieldTypes head →
      WellKinded program.declarations context.static type .type → AtomType program context (.construct type variant fields) type
  | closure {id arguments captures function} : Instance program id arguments function →
      CapturesType program.declarations context captures (function.captures.map (·.type)) →
      AtomType program context (.closure id arguments captures) (.callable id arguments)
  | function {id arguments signature} : CallSignature program.declarations context.static id arguments signature →
      AtomType program context (.function id arguments) (.callable id arguments)
  | operation {id family item operation signature} : program.declarations.operation id = some operation →
      CallSignature program.declarations context.static id (family ++ item) signature →
      AtomType program context (.operation id family item) (.callable id (family ++ item))
  | label {id region type} : (id,region,type) ∈ context.labels →
      AtomType program context (.label (.rigid id .brand 0)) (.label (.rigid id .brand 0) region type)
  | primitive {id arguments operands binding substitution signature} : binding ∈ program.declarations.input.manifest.bindings →
      binding.declaration = id → Instantiates binding.signature.generics arguments substitution →
      signature = binding.signature.instantiate substitution →
      binding.ScalarSignature program.declarations.input.target arguments signature →
      PlacesType program.declarations context operands signature.parameters →
      (signature.unsafeAllowed = true → context.static.unsafeAllowed = true) →
      RowSubset program.declarations context.static signature.effects context.effects →
      AtomType program context (.primitive id arguments operands) signature.result
  | available {place brand region residents writable} :
      PlaceType program.declarations context place (.available brand region residents) writable →
      AtomType program context (.available place) (.available brand region residents)
  | bindings {place brand region arguments writable} : PlaceType program.declarations context place (.bindings brand region arguments) writable →
      AtomType program context (.bindings place) (.bindings brand region arguments)

mutual
  inductive ValueTyped (program : Kernel.Program) (world : World) : Value → Prop where
    | unit {owner live} : ValueTyped program world (.resident owner .unit .unit live [])
    | scalar {owner value live} : value.Valid program.declarations.input.target →
        ValueTyped program world (.resident owner (.scalar value.type) (.scalar value) live [])
    | aggregate {owner type head live fields types} : Execution.ConstructorHead program.declarations type
        (match head with | .constructor id => some id | _ => none) types head →
        FieldsTyped program world fields types → ValueTyped program world (.resident owner type head live fields)
    | reference {owner mode region type id loan live} : world.loans.get id = some loan → loan.live = true → loan.mode = mode →
        region = .runtimeRegion loan.region →
        AddressType program.declarations world loan.referent type →
        ValueTyped program world (.resident owner (.reference mode region type) (.reference id) live [])
    | pointer {owner mode type pointer live} : pointer.address < 2^program.declarations.input.target.pointerBits →
        pointer.Origin world →
        ValueTyped program world (.resident owner (.rawPointer mode type) (.pointer pointer) live [])
    | callable {owner id arguments live fields function} : Instance program id arguments function →
        FieldsTyped program world fields (function.captures.map (·.type)) →
        ValueTyped program world (.resident owner (.callable id arguments) (.callable id arguments) live fields)
    | operation {owner id arguments live operation signature} : Execution.OperationInstance program id arguments operation signature →
        ValueTyped program world (.resident owner (.callable id arguments) (.operation id arguments) live [])
    | label {owner brand region result live} : ValueTyped program world
        (.resident owner (.label (.runtimeBrand (.label brand)) region result) (.label brand) live [])
    | continuation {owner type id live} : (∃ argument answer effects quantity,
        type = .continuation (.runtimeBrand (.resumption id)) argument answer effects quantity) →
        ValueTyped program world (.resident owner type (.continuation id) live [])
    | available {owner brand region residents id live available} : world.availability.get id = some available → available.brand = brand →
        brand = .runtimeBrand (.proof id) → region = .runtimeRegion available.region →
        residents = available.residents →
        ValueTyped program world (.resident owner (.available brand region residents) (.available id) live [])
    | bindings {owner brand region live fields types pack} : FieldsTyped program world fields types →
        brand = .runtimeBrand (.proof pack.brand) → region = .runtimeRegion pack.region →
        fields.length = pack.fields.length → pack.fields.Nodup →
        ValueTyped program world (.resident owner (.bindings brand region types) (.bindings pack) live fields)

  inductive FieldsTyped (program : Kernel.Program) (world : World) : List (Option Value) → List Term → Prop where
    | nil : FieldsTyped program world [] []
    | hole {fields type types} : FieldsTyped program world fields types → FieldsTyped program world (none :: fields) (type :: types)
    | resident {value fields type types} : ValueTyped program world value → value.type = type →
        FieldsTyped program world fields types → FieldsTyped program world (some value :: fields) (type :: types)
end

def WorldTyped (program : Kernel.Program) (world : World) : Prop :=
  world.WellFormed ∧ (∀ address value, world.Resident address value → ValueTyped program world value) ∧
  (∀ id root value, world.roots.get id = some root → root.value = some value → value.type = root.type) ∧
  (∀ id root, world.roots.get id = some root → root.type.RuntimeRegionsBelow world.nextRegion)

def PatternCoverage (program : Kernel.Program) (type : Term) (arms : List Arm) : Prop :=
  (∀ world address value, WorldTyped program world → world.Stores address value → value.type = type → value.Initialized →
    ∃ arm, FirstArm program.declarations world address arms arm) ∧
  (∀ arm ∈ arms, ∃ world address value, WorldTyped program world ∧ world.Stores address value ∧ value.type = type ∧
    value.Initialized ∧ FirstArm program.declarations world address arms arm)

/-- Removing an effect family from the outward row requires coverage of every
admissible operation application and initialized payload, not merely one arm
whose operation happens to belong to that family. Partial handlers forward. -/
def CompletelyHandles (program : Kernel.Program) (context : Language.Context)
    (handler : Handler) (instanceTerm : Term) : Prop :=
  ∃ id arguments family substitution,
    instanceTerm = .effect id arguments ∧ program.declarations.effect id = some family ∧
    Instantiates family.generics arguments substitution ∧ ConstraintsHold program.declarations context substitution family.requirements ∧
    ∀ operationId ∈ family.operations, ∀ itemArguments operation signature,
      Execution.OperationInstance program operationId (arguments ++ itemArguments) operation signature →
      ∀ world payload, WorldTyped program world →
        ListRel (fun source type => Permitted world source.authority .shared source.address ∧
          ∃ value, world.Stores source.address value ∧ value.type = type ∧ value.Initialized)
          payload signature.parameters →
        ∃ arm ∈ handler.operations, Execution.ArmAccepts program world context operationId (arguments ++ itemArguments) payload arm

def HandledInstances (program : Kernel.Program) (context : Language.Context)
    (handler : Handler) (instances : List Term) : Prop :=
  ∀ instanceTerm ∈ instances, CompletelyHandles program context handler instanceTerm

mutual
  inductive CodeType (program : Kernel.Program) : Context → Code → Term → Prop where
    | result {context place actual result writable} : PlaceType program.declarations context place actual writable →
        Subtype program.declarations context.static actual result → CodeType program context (.result place) result
    | bind {context localSlot atom next result} : AtomType program context atom localSlot.type →
        CodeType program (context.bind localSlot) next result → CodeType program context (.bind localSlot atom next) result
    | evaluate {context localSlot code next result} : CodeType program context code localSlot.type →
        CodeType program (context.bind localSlot) next result → CodeType program context (.evaluate localSlot code next) result
    | assign {context destination source next type writable result} : PlaceType program.declarations context destination type true →
        PlaceType program.declarations context source type writable → CodeType program context next result →
        CodeType program context (.assign destination source next) result
    | discard {context place next type writable result} : PlaceType program.declarations context place type writable →
        CodeType program context next result → CodeType program context (.discard place next) result
    | invoke {context localSlot call next result} : InvocationType program.declarations context call →
        Subtype program.declarations context.static call.signature.result localSlot.type → CodeType program (context.bind localSlot) next result →
        CodeType program context (.invoke localSlot call next) result
    | tail {context call result} : InvocationType program.declarations context call →
        Subtype program.declarations context.static call.signature.result result → CodeType program context (.tail call) result
    | scope {context id body result} : CodeType program context body result → CodeType program context (.scope id body) result
    | label {context brand region type body} :
        CodeType program { context with labels := (brand,.rigid region .region 0,type) :: context.labels } body type →
        CodeType program context (.label brand region type body) type
    | choose {context subject arms type writable result} : PlaceType program.declarations context subject type writable →
        PatternCoverage program type arms → ArmsType program context arms type result →
        CodeType program context (.choose subject arms) result
    | handler {context id computation handler input result instances} : HandlerType program context handler input result →
        HandledInstances program context.static handler instances →
        CodeType program { context with effects := .row instances [context.effects] } computation input →
        CodeType program context (.handle id computation handler) result
    | test {context localSlot subject pattern id next type writable bindings result carrier arguments} :
        PlaceType program.declarations context subject type writable →
        PatternType program.declarations context.static pattern type .shared bindings →
        program.declarations.input.manifest.testCarrier = some carrier → localSlot.type = .nominal carrier.declaration arguments →
        CodeType program (context.bind localSlot) next result → CodeType program context (.test localSlot subject pattern id next) result
    | endLoan {context handle next mode region type writable result} :
        PlaceType program.declarations context handle (.reference mode region type) writable →
        CodeType program context next result → CodeType program context (.endLoan handle next) result
    | unsafeAllowed {context body result} : CodeType program { context with static := { context.static with unsafeAllowed := true } } body result →
        CodeType program context (.unsafeScope body) result
    | closeAvailable {context place next brand region residents writable result} :
        PlaceType program.declarations context place (.available brand region residents) writable → CodeType program context next result →
        CodeType program context (.closeAvailable place next) result
    | reserve {context localSlot brand places next types result region} :
        ListRel (fun place type => ∃ writable, PlaceType program.declarations context place type writable) places types →
        localSlot.type = .available (.rigid brand .brand 0) region types → CodeType program (context.bind localSlot) next result →
        CodeType program context (.reserve localSlot brand places next) result
    | abort {context result} : CodeType program context .abort result
    | bottom {context code result} : CodeType program context code .bottom → CodeType program context code result

  inductive ArmsType (program : Kernel.Program) : Context → List Arm → Term → Term → Prop where
    | nil {context input output} : ArmsType program context [] input output
    | cons {context pattern body arms input output bindings} :
        PatternType program.declarations context.static pattern input .owned bindings → (bindings.map (·.id)).Nodup →
        CodeType program { context with locals := bindings ++ context.locals } body output → ArmsType program context arms input output →
        ArmsType program context (.clause pattern body :: arms) input output

  inductive HandlerType (program : Kernel.Program) : Context → Handler → Term → Term → Prop where
    | attached {context result completion operations captures input types} : CapturesType program.declarations context captures types →
        CompletionType program { context with locals := Execution.CaptureLocals captures } completion input result →
        OperationArmsType program { context with locals := Execution.CaptureLocals captures } operations result →
        HandlerType program context (.attached result completion operations captures) input result

  inductive CompletionType (program : Kernel.Program) : Context → List Arm → Term → Term → Prop where
    | identity {context input result} : Equal program.declarations context.static input result →
        CompletionType program context [] input result
    | arms {context completion input result} : completion ≠ [] → PatternCoverage program input completion →
        ArmsType program context completion input result → CompletionType program context completion input result

  inductive OperationArmsType (program : Kernel.Program) : Context → List OperationArm → Term → Prop where
    | nil {context result} : OperationArmsType program context [] result
    | cons {context id family item patterns continuation body rest result operation signature bindings output} :
        Execution.OperationInstance program id (family ++ item) operation signature →
        PatternsType program.declarations context.static patterns signature.parameters .owned bindings →
        ((operation.terminal = true ∧ continuation = none ∧ output = result) ∨
          (operation.terminal = false ∧ ∃ quantity, operation.quantity = some quantity ∧
            ((continuation = none ∧ quantity.Contains 1 ∧ output = signature.result) ∨
              (∃ localSlot brand, continuation = some localSlot ∧
                localSlot.type = .continuation (.rigid brand .brand 0) signature.result result signature.effects quantity ∧ output = result)))) →
        CodeType program { context with locals := bindings ++ continuation.toList ++ context.locals } body output →
        OperationArmsType program context rest result →
        OperationArmsType program context (.clause id family item patterns continuation body :: rest) result
end

def FunctionType (program : Kernel.Program) (function : Function) : Prop :=
  ∃ declaration,
    program.declarations.function function.declaration = some declaration ∧
    (function.parameters.map (·.type)) = function.signature.parameters ∧
    (function.parameters.map (·.id)).Nodup ∧ (function.captures.map (·.id)).Nodup ∧
    (∀ formal ∈ function.parameters, ∀ capture ∈ function.captures, formal.id ≠ capture.id) ∧
    CodeType program ⟨⟨function.signature.generics,function.signature.constraints,0,declaration.header.module,false⟩,
      function.captures ++ function.parameters,
      function.namedExit.toList.map (fun id => (id,.rigid function.activationRegion .region 0,function.signature.result)),function.signature.effects,none⟩
      function.body function.signature.result

end Glorious.Language.Typing
