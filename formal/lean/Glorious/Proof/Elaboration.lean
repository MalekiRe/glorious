import Glorious.Semantics.Elaborate
import Glorious.Proof.Operational

namespace Glorious.Semantics.Spec

structure SourceContext where
  module : ModuleId
  locals : List Local
  labels : List (String × Term)
  permitted : Term
  unsafePermission : Bool

def FreshSlots (context : SourceContext) (slots : List TypedSlot) : Prop :=
  (slots.map (·.id)).Nodup ∧
  ∀ slot ∈ slots, ∀ localValue ∈ context.locals, slot.id ≠ localValue.id

def Produces (slot : TypedSlot) (operation : CoreOp) : Core :=
  .step (.declare slot) (.step operation (.result ⟨slot.id, []⟩))

def Binds (values : List (TypedSlot × Core)) (next : Core) : Core :=
  values.foldr (fun (slot, computation) next => .bind slot computation next) next

inductive DeclarationHeader (program : Program) : DeclHeader → Prop where
  | function {item} : item ∈ program.functions → DeclarationHeader program item.header
  | dataType {item} : item ∈ program.dataTypes → DeclarationHeader program item.header
  | variant {item variant} : item ∈ program.dataTypes → variant ∈ item.variants → DeclarationHeader program variant.header
  | field {item variant field} : item ∈ program.dataTypes → variant ∈ item.variants →
      field ∈ variant.fields → DeclarationHeader program field.header
  | alias {item} : item ∈ program.aliases → DeclarationHeader program item.header
  | traitDecl {item} : item ∈ program.traits → DeclarationHeader program item.header
  | effect {item} : item ∈ program.effects → DeclarationHeader program item.header
  | operation {item operation} : item ∈ program.effects → operation ∈ item.operations → DeclarationHeader program operation.header
  | constant {item} : item ∈ program.constants → DeclarationHeader program item.header

inductive Resolves (program : Program) (bindings : List Binding) (module : ModuleId)
    (nameSpace : Namespace) (path : Path) : DeclId → Prop where
  | selected {binding header}
      (present : binding ∈ bindings) (scope : binding.module = module)
      (space : binding.nameSpace = nameSpace)
      (spelling : path.components = [binding.name])
      (declaration : binding.declaration = header.id)
      (declared : DeclarationHeader program header)
      (authority : ModuleMaySee module header)
      (unique : ∀ other ∈ bindings, other.module = module → other.nameSpace = nameSpace →
        other.name = binding.name → other.priority ≥ binding.priority → other.declaration = binding.declaration) :
      Resolves program bindings module nameSpace path binding.declaration

/- The binding inventory is derived from the selected pattern. It cannot add
an arbitrary local or select a different field with an equal type. -/
mutual
inductive PatternLocals : CheckedPattern → List Projection → Bool → List Local → List PatternBinding → Prop where
  | wildcard {type path mutable} : PatternLocals (.wildcard type) path mutable [] []
  | binder {identity name type path mutable} :
      PatternLocals (.binder identity name type) path mutable
        [⟨identity, name, type, mutable, 0⟩] [⟨⟨identity, type, mutable, {}⟩, path, none⟩]
  | constructor {type key patterns path mutable locals bindings}
      (children : PatternLocalFields patterns
        (match key with | .constructor declaration => path ++ [.variant declaration] | _ => path)
        0 mutable locals bindings) :
      PatternLocals (.constructor type key patterns) path mutable locals bindings

inductive PatternLocalFields : List CheckedPattern → List Projection → Nat → Bool → List Local → List PatternBinding → Prop where
  | nil {path index mutable} : PatternLocalFields [] path index mutable [] []
  | cons {pattern patterns path index mutable locals bindings restLocals restBindings}
      (head : PatternLocals pattern (path ++ [.field index]) mutable locals bindings)
      (tail : PatternLocalFields patterns path (index + 1) mutable restLocals restBindings) :
      PatternLocalFields (pattern :: patterns) path index mutable (locals ++ restLocals) (bindings ++ restBindings)
end

inductive Callable (program : CoreProgram) : Term → Signature → Prop where
  | function {function arguments substitution signature}
      (present : function ∈ program.source.functions)
      (instantiation : Instantiates function.signature.generics arguments substitution)
      (inputs : Glorious.Proof.Forall₂ (Substitutes substitution) function.signature.arguments signature.arguments)
      (output : Substitutes substitution function.signature.output signature.output)
      (effects : Substitutes substitution function.signature.effects signature.effects)
      (safety : signature.unsafeCall = function.signature.unsafeCall)
      (abi : signature.abi = function.signature.abi) :
      Callable program (.callable function.header.id arguments) signature
  | label {brand region output} :
      Callable program (.label brand region output)
        { arguments := [output], output := .bottom, effects := .row [] [] }
  | continuation {identity argument output effects} :
      Callable program (.continuation identity argument output effects)
        { arguments := [argument], output, effects }
  | shared {type signature region}
      (underlying : Callable program type signature)
      (mode : signature.receiver = some .shared) :
      Callable program (.reference .shared region type) signature
  | unique {type signature region}
      (underlying : Callable program type signature)
      (mode : signature.receiver = some .shared ∨ signature.receiver = some .unique) :
      Callable program (.reference .unique region type) signature

inductive PatternElaborates (program : CoreProgram) (context : SourceContext) :
    Pattern → Term → CheckedPattern → Prop where
  | wildcard {type} : PatternElaborates program context .wildcard type (.wildcard type)
  | binder {identity name type forced}
      (fresh : ∀ localValue ∈ context.locals, identity ≠ localValue.id)
      (binding : forced = true ∨ ¬ ∃ declaration, Resolves program.source program.bindings context.module .value ⟨[name]⟩ declaration) :
      PatternElaborates program context (.binder identity name forced) type (.binder identity name type)
  | tuple {patterns types checked}
      (children : Glorious.Proof.Forall₂ (fun pair checked => PatternElaborates program context pair.1 pair.2 checked)
        (patterns.zip types) checked)
      (arity : patterns.length = types.length) :
      PatternElaborates program context (.tuple patterns) (.tuple types) (.constructor (.tuple types) (.product types.length) checked)
  | scalar {value} (valid : ValidScalar program.source.target value)
      (structural : ∀ width bits, value ≠ .floating width bits) :
      PatternElaborates program context (.constant (.constant value)) (scalarValueType value)
        (.constructor (scalarValueType value) (.scalar value) [])
  | nominal {declaration fields rest data variant arguments substitution types checked}
      (selected : program.source.constructor declaration = some (data, variant))
      (instantiation : Instantiates data.generics arguments substitution)
      (fieldTypes : Glorious.Proof.Forall₂ (Substitutes substitution) (variant.fields.map (·.type)) types)
      (privacy : ∀ field ∈ variant.fields, ModuleMaySee context.module field.header)
      (noDrop : data.dropHook = none)
      (authority : data.nonExhaustive = false ∨ context.module.packageId = data.header.id.packageId)
      (arity : checked.length = types.length)
      (fieldsValid : ∀ index type pattern result, types[index]? = some type →
        (index, pattern) ∈ fields → checked[index]? = some result → PatternElaborates program context pattern type result)
      (omitted : ∀ index type, types[index]? = some type →
        (¬ ∃ pattern, (index, pattern) ∈ fields) → rest = true ∧ checked[index]? = some (.wildcard type)) :
      PatternElaborates program context (.constructor declaration fields rest) (.nominal data.header.id arguments)
        (.constructor (.nominal data.header.id arguments) (.constructor declaration) checked)

mutual
  inductive Elaborates (program : CoreProgram) : SourceContext → Expr → Term → Core → Prop where
    | unit {context span slot} (type : slot.type = .unit) (fresh : FreshSlots context [slot]) :
        Elaborates program context (.unit span) .unit (Produces slot (.constant slot.id (.constantTuple [])))
    | integer {context span magnitude suffix negative signed width slot}
        (type : slot.type = .scalar (.integer signed width))
        (suffixAgrees : suffix = none ∨ suffix = some (.integer signed width))
        (valid : ValidScalar program.source.target
          (.integer signed width (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude)))
        (fresh : FreshSlots context [slot]) :
        Elaborates program context (.literal span (.integer magnitude suffix negative)) slot.type
          (Produces slot (.constant slot.id (.constant
            (.integer signed width (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude)))))
    | character {context span scalar slot}
        (type : slot.type = .scalar .character)
        (valid : ValidScalar program.source.target (.character scalar))
        (fresh : FreshSlots context [slot]) :
        Elaborates program context (.literal span (.character scalar)) slot.type
          (Produces slot (.constant slot.id (.constant (.character scalar))))
    | localValue {context span identity localValue slot}
        (declared : localValue ∈ context.locals) (same : localValue.id = identity)
        (type : slot.type = localValue.type) (fresh : FreshSlots context [slot]) :
        Elaborates program context (.localValue span identity) slot.type
          (Produces slot (.read slot.id ⟨identity, []⟩ false))
    | localName {context span path localValue type code}
        (declared : localValue ∈ context.locals) (spelling : path.components = [localValue.name])
        (body : Elaborates program context (.localValue span localValue.id) type code) :
        Elaborates program context (.name span path []) type code
    | functionName {context span path explicit declaration arguments slot signature}
        (resolved : Resolves program.source program.bindings context.module .value path declaration)
        (callable : Callable program (.callable declaration arguments) signature)
        (explicitPreserved : explicit.IsPrefix arguments)
        (type : slot.type = .callable declaration arguments) (fresh : FreshSlots context [slot]) :
        Elaborates program context (.name span path explicit) slot.type
          (Produces slot (.closure slot.id declaration arguments [] true))
    | tuple {context span expressions values slot}
        (fields : ElaboratesArguments program context expressions values)
        (type : slot.type = .tuple (values.map (·.1.type)))
        (fresh : FreshSlots context (slot :: values.map (·.1))) :
        Elaborates program context (.tuple span expressions) slot.type
          (Binds values (Produces slot (.construct slot.id none (values.map (fun value => ⟨value.1.id, []⟩)))))
    | apply {context span callee arguments calleeSlot calleeCode inputs signature output call}
        (receiver : Elaborates program context callee calleeSlot.type calleeCode)
        (callable : Callable program calleeSlot.type signature)
        (operands : ElaboratesArguments program context arguments inputs)
        (types : Glorious.Proof.Forall₂ (fun input type => Subtype program.source [] input.1.type type) inputs signature.arguments)
        (effects : RowIncludes program.source context.permitted signature.effects)
        (safety : signature.unsafeCall = true → context.unsafePermission = true)
        (outputType : output.type = signature.output)
        (selected : call.callee = ⟨calleeSlot.id, []⟩ ∧ call.signature = signature ∧
          call.inputs = inputs.zipIdx.map (fun ((slot, _), index) => ⟨.argument index, ⟨slot.id, []⟩, slot.type⟩))
        (fresh : FreshSlots context (output :: calleeSlot :: inputs.map (·.1))) :
        Elaborates program context (.apply span callee arguments) signature.output
          (Binds ((calleeSlot, calleeCode) :: inputs) (Produces output (.invoke output.id call)))
    | tail {context span callee arguments receiver body inputs signature call}
        (calleeProof : Elaborates program context callee receiver.type body)
        (callable : Callable program receiver.type signature)
        (operands : ElaboratesArguments program context arguments inputs)
        (types : Glorious.Proof.Forall₂ (fun input type => Subtype program.source [] input.1.type type) inputs signature.arguments)
        (effects : RowIncludes program.source context.permitted signature.effects)
        (safety : signature.unsafeCall = true → context.unsafePermission = true)
        (selected : call.callee = ⟨receiver.id, []⟩ ∧ call.signature = signature ∧
          call.inputs = inputs.zipIdx.map (fun ((slot, _), index) => ⟨.argument index, ⟨slot.id, []⟩, slot.type⟩)) :
        Elaborates program context (.tail span callee arguments) .bottom
          (Binds ((receiver, body) :: inputs) (.tail call))
    | unsafeScope {context : SourceContext} {span body type code}
        (bodyProof : Elaborates program { context with unsafePermission := true } body type code) :
        Elaborates program context (.unsafeScope span body) type code
    | block {context span statements result type code scope}
        (body : ElaboratesBlock program context statements result type code) :
        Elaborates program context (.block span statements result) type (.scopeBlock scope code)
    | label {context : SourceContext} {span identity name annotation type body code brand region}
        (fresh : brand = .rigid identity .brand 1 ∧ region = .rigid identity .region 1)
        (annotationAgrees : annotation = none ∨ annotation = some type)
        (bodyProof : Elaborates program
          { context with labels := (name, .label brand region type) :: context.labels } body type code) :
        Elaborates program context (.label span identity name annotation body) type (.label identity brand region type code)
    | coercion {context expression actual expected code}
        (body : Elaborates program context expression actual code)
        (subtype : Subtype program.source [] actual expected) :
        Elaborates program context expression expected code

  inductive ElaboratesArguments (program : CoreProgram) :
      SourceContext → List Expr → List (TypedSlot × Core) → Prop where
    | nil {context} : ElaboratesArguments program context [] []
    | cons {context expression expressions slot code rest}
        (head : Elaborates program context expression slot.type code)
        (tail : ElaboratesArguments program context expressions rest) :
        ElaboratesArguments program context (expression :: expressions) ((slot, code) :: rest)

  inductive ElaboratesBlock (program : CoreProgram) :
      SourceContext → List Statement → Option Expr → Term → Core → Prop where
    | result {context expression type code} (body : Elaborates program context expression type code) :
        ElaboratesBlock program context [] (some expression) type code
    | unit {context code} (body : Elaborates program context (.unit {}) .unit code) :
        ElaboratesBlock program context [] none .unit code
    | discard {context span expression statements result slot valueCode type code}
        (value : Elaborates program context expression slot.type valueCode)
        (rest : ElaboratesBlock program context statements result type code) :
        ElaboratesBlock program context (.discard span expression :: statements) result type
          (.bind slot valueCode (.step (.discard ⟨slot.id, []⟩) code))
    | binding {context span pattern mutable annotation expression statements result slot valueCode checked bindings locals nextContext type code}
        (value : Elaborates program context expression slot.type valueCode)
        (annotationValid : ∀ expected, annotation = some expected → Subtype program.source [] slot.type expected)
        (patternProof : PatternElaborates program context pattern slot.type checked)
        (bindingPaths : PatternLocals checked [] mutable locals bindings)
        (scope : nextContext = { context with locals := locals ++ context.locals })
        (rest : ElaboratesBlock program nextContext statements result type code) :
        ElaboratesBlock program context (.binding span pattern mutable annotation expression :: statements) result type
          (.bind slot valueCode (coreStepList (bindings.map (fun binding => .declare binding.slot))
            (.step (.deconstruct ⟨slot.id, []⟩ checked bindings)
              (.step (.seal (bindings.map (fun binding => ⟨binding.slot.id, []⟩))) code))))
end

structure ElaborationCorrect (source : Program) (core : CoreProgram) : Prop where
  declarations : ProgramWellFormed core.source
  preservedIdentity : ∀ declaration ∈ source.functions,
    ∃ lowered ∈ core.source.functions, lowered.header = declaration.header
  functions : ∀ declaration ∈ source.functions, ∀ body, declaration.body = some body →
    ∃ function ∈ core.functions, function.declaration = declaration.header.id ∧
      function.signature = declaration.signature ∧
      ∃ context : SourceContext, ∃ code identity brand region,
        context.module = declaration.header.module ∧ context.permitted = declaration.signature.effects ∧
        context.unsafePermission = false ∧ context.labels = [] ∧
        context.locals = (declaration.parameters.zip function.parameters).map
          (fun (parameter, slot) => ⟨slot.id, parameter.name, slot.type, parameter.mutable, 0⟩) ∧
        Elaborates core context body function.signature.output code ∧
        function.body = .label identity brand region function.signature.output code
  storageBindings : ∀ function ∈ core.functions,
    (function.parameters.map (·.id)).Nodup ∧ (function.captures.map (·.parameter)).Nodup

end Glorious.Semantics.Spec
