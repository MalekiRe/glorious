import Glorious.Semantics.VM

namespace Glorious.Semantics

structure Lowering where
  analyzed : AnalyzedProgram
  artifact : VM.Artifact
  typeIds : List (Term × Nat) := []
  protocolIds : List (Term × Nat) := []
  functionIds : List (DeclId × Nat) := []
  importIds : List (DeclId × Nat) := []
  pending : List CoreFunction := []
  nextSynthetic : Nat := 3000000000
  deriving Repr

abbrev LowerM := StateT Lowering Check

def declarationName (declaration : DeclId) : String := s!"g{declaration.packageId}_{declaration.localId}"
def typeName (type : Term) : String := toString (repr type)
def receiverNumber : ReceiverMode → Nat | .shared => 0 | .unique => 1 | .owned => 2

def builtinTypes : List VM.Type :=
  ["Unit", "Never", "U8", "U16", "U32", "U64", "U128", "I8", "I16", "I32", "I64", "I128",
    "Usize", "Isize", "F32", "F64", "Char", "Text", "Bytes"].map VM.Type.builtin

def builtinId : Term → Option Nat
  | .unit => some 0 | .bottom => some 1
  | .scalar (.integer false .w8) => some 2 | .scalar (.integer false .w16) => some 3
  | .scalar (.integer false .w32) => some 4 | .scalar (.integer false .w64) => some 5
  | .scalar (.integer false .w128) => some 6 | .scalar (.integer true .w8) => some 7
  | .scalar (.integer true .w16) => some 8 | .scalar (.integer true .w32) => some 9
  | .scalar (.integer true .w64) => some 10 | .scalar (.integer true .w128) => some 11
  | .scalar (.integer false .pointer) => some 12 | .scalar (.integer true .pointer) => some 13
  | .scalar (.floating .w32) => some 14 | .scalar (.floating .w64) => some 15
  | .scalar .character => some 16
  | .label .. | .environment .. | .available .. => some 0
  | _ => none

def captureResidentType (capture : Capture) : Term :=
  match capture.mode with
  | .owned => capture.type
  | .shared => .reference .shared (.rigid capture.parameter .region 0) capture.type
  | .unique => .reference .unique (.rigid capture.parameter .region 0) capture.type

mutual
  def lowerType : Nat → Term → LowerM Nat
    | 0, _ => reject .resourceLimit "VM concrete-type lowering exhausted"
    | fuel + 1, original => do
      let state ← get
      let program := state.analyzed.core.source
      let type ← normalize program state.analyzed.core.inference program.limits.normalization [] original
      if let some id := builtinId type then return id
      if let some id := lookup type state.typeIds then return id
      let _ ← layoutOf program state.analyzed.core.inference program.limits.layout [] type
      let id := state.artifact.types.length
      modify fun state => { state with typeIds := state.typeIds ++ [(type, id)],
        artifact.types := state.artifact.types ++ [.builtin "Unit"] }
      let capability ← deriveUse program state.analyzed.core.inference type
      let copy := capability == .duplicable
      let discard := capability != .exact
      let representation ← match type with
        | .tuple fields => pure (.tuple (← fields.mapM (lowerType fuel)) copy)
        | .array element (.constant (.integer _ _ count)) =>
          let element ← lowerType fuel element
          require (count ≥ 0 && count.toNat ≤ program.limits.alternatives) .resourceLimit "fixed array lowering exceeds resident limit"
          pure (.tuple (List.replicate count.toNat element) copy)
        | .rawPointer _ referent =>
          pure (.record (typeName type) [⟨s!"address:{typeName referent}", 12⟩] true)
        | .reference mode _ referent =>
          modify fun state => { state with artifact.requiredFeatures := Nat.lor state.artifact.requiredFeatures 2 }
          pure (.reference (mode == .unique) (← lowerType fuel referent))
        | .nominal declaration arguments =>
          let data ← getRequired (program.dataType declaration) .unknownName "unknown nominal VM type"
          let subs ← bindArguments data.generics arguments
          let variants ← data.variants.mapM fun variant => do
            let fields ← variant.fields.mapM fun field => do
              let type ← substitute program.limits.normalization subs field.type
              return (⟨declarationName field.header.id, ← lowerType fuel type⟩ : VM.Field)
            return (⟨declarationName variant.header.id, fields, none⟩ : VM.Variant)
          if data.isEnum then pure (.enumeration (typeName type) variants copy) else
            pure (.record (typeName type) (variants.headD ⟨"", [], none⟩).fields copy)
        | .callable declaration arguments =>
          let coreFunction := state.analyzed.core.function declaration
          let (signature, _) ← declarationSignature program declaration
          let subs ← bindArguments signature.generics arguments
          let signature ← substituteSignature program.limits.normalization subs signature
          let captureTypes := coreFunction.map (fun f => f.captures.map captureResidentType) |>.getD []
          let captures ← lowerType fuel (.tuple captureTypes)
          let classes ← captureTypes.mapM (deriveUse program state.analyzed.core.inference)
          let class := Principal.residents classes
          let mode := coreFunction.map (fun f => receiverNumber f.receiver) |>.getD 0
          pure (.callable (← lowerSignature fuel signature) captures mode (typeName type)
            (class == .duplicable) (class != .exact))
        | .continuation identity argument output effects =>
          modify fun state => { state with artifact.requiredFeatures := Nat.lor state.artifact.requiredFeatures 8 }
          pure (.resumption (← lowerType fuel argument) (← lowerType fuel output)
            ⟨[], ← lowerType fuel output, ← lowerRow fuel effects⟩ 1 (some 1) s!"k{identity}" false)
        | .bindings _ _ fields => pure (.bindings (← lowerType fuel (.tuple fields)) (typeName type) copy)
        | _ => reject .missingEvidence "VM lowering received a non-runtime or unresolved type"
      let representation := match representation with
        | .reference .. | .callable .. | .resumption .. => representation
        | _ => VM.Type.restricted representation copy discard
      modify fun state => { state with artifact.types := state.artifact.types.set id representation }
      return id

  def lowerSignature (fuel : Nat) (signature : Signature) : LowerM VM.Signature := do
    return ⟨← signature.arguments.mapM (lowerType fuel), ← lowerType fuel signature.output,
      ← lowerRow fuel signature.effects⟩

  def lowerRow (fuel : Nat) (row : Term) : LowerM (List Nat) := do
    match row with
    | .row instances [] => return (← instances.mapM (lowerProtocol fuel)).eraseDups
    | _ => reject .missingEvidence "VM signature contains an open effect row"

  def lowerProtocol : Nat → Term → LowerM Nat
    | 0, _ => reject .resourceLimit "effect protocol lowering exhausted"
    | fuel + 1, effectInstance => do
      let state ← get
      if let some id := lookup effectInstance state.protocolIds then return id
      let .effect declaration arguments := effectInstance | reject .kindMismatch "protocol key is not an effect instance"
      let program := state.analyzed.core.source
      let effect ← getRequired (program.effects.find? (fun e => e.header.id == declaration)) .unknownName "unknown effect protocol"
      let subs ← bindArguments effect.generics arguments
      let id := state.artifact.protocols.length
      modify fun state => { state with protocolIds := state.protocolIds ++ [(effectInstance, id)],
        artifact.protocols := state.artifact.protocols ++ [⟨typeName effectInstance, [], []⟩],
        artifact.requiredFeatures := Nat.lor state.artifact.requiredFeatures 8 }
      let operations ← effect.operations.mapM fun operation => do
        let signature ← substituteSignature program.limits.normalization subs operation.signature
        let terminal := operation.signature.output == .bottom
        let (lower, upper) := if terminal then (0, none) else operation.quantity.getD (1, some 1)
        if upper.getD 0 > 1 then modify fun s => { s with artifact.requiredFeatures := Nat.lor s.artifact.requiredFeatures 16 }
        return (⟨declarationName operation.header.id, ← lowerSignature fuel { signature with effects := .row [] [] },
          ← lowerType fuel signature.output, lower, upper, terminal⟩ : VM.Operation)
      let typeArguments ← arguments.filter (fun t => t.kind == .type) |>.mapM (lowerType fuel)
      modify fun state => { state with artifact.protocols := state.artifact.protocols.set id ⟨typeName effectInstance, typeArguments, operations⟩ }
      return id
end

def internConstant (constant : VM.Constant) : LowerM Nat := do
  let state ← get
  if let some id := state.artifact.constants.findIdx? (· == constant) then return id
  let id := state.artifact.constants.length
  set { state with artifact.constants := state.artifact.constants ++ [constant] }
  return id

structure RegisterInfo where
  source : Id
  register : Nat
  type : Term
  flag : Nat
  deriving Repr

structure FunctionLowering where
  global : Lowering
  function : CoreFunction
  registers : List Nat := [0]
  locals : List RegisterInfo := []
  code : List VM.Instruction := []
  labels : List (Term × Nat × Nat) := []
  nextLabel : Nat := 0
  deriving Repr

abbrev EmitM := StateT FunctionLowering Check

def global (action : LowerM α) : EmitM α := do
  let state ← get
  let (value, global) ← action.run state.global
  set { state with global }
  return value

def emit (instruction : VM.Instruction) : EmitM Nat := do
  let state ← get
  let cursor := state.code.length
  set { state with code := state.code ++ [instruction] }
  return cursor

def patch (cursor : Nat) (instruction : VM.Instruction) : EmitM Unit :=
  modify fun state => { state with code := state.code.set cursor instruction }

def temporary (type : Nat) : EmitM Nat := do
  let state ← get
  let register := state.registers.length
  set { state with registers := state.registers ++ [type] }
  return register

def setFlag (info : RegisterInfo) (initialized : Bool) : EmitM Unit := do
  let constant ← global (internConstant (.scalar (.integer false .w32 (if initialized then 1 else 0))))
  let _ ← emit (.constant info.flag constant)
  pure ()

def allocateRegister (slot : TypedSlot) (parameter : Bool := false) : EmitM RegisterInfo := do
  let state ← get
  require (!(state.locals.any (fun local => local.source == slot.id))) .duplicate "VM slot allocated twice"
  let type ← global (lowerType state.global.analyzed.core.source.limits.layout slot.type)
  let register ← temporary type
  let flag ← temporary 4
  let info : RegisterInfo := ⟨slot.id, register, slot.type, flag⟩
  modify fun state => { state with locals := state.locals ++ [info] }
  setFlag info parameter
  return info

def localRegister (identity : Id) : EmitM RegisterInfo := do
  getRequired ((← get).locals.find? (fun local => local.source == identity)) .malformedCore "typed Core refers to an unallocated VM slot"

def conditionalDrop (info : RegisterInfo) : EmitM Unit := do
  let one ← global (internConstant (.scalar (.integer false .w32 1)))
  let branch ← emit (.nop)
  let yes := (← get).code.length
  let _ ← emit (.drop info.register)
  setFlag info false
  let end_ := (← get).code.length
  patch branch (.switch info.flag [(one, yes)] end_)

def cleanupRegisters (registers : List RegisterInfo) (protected : List Nat := []) : EmitM Unit := do
  for register in registers.reverse do
    if !protected.contains register.register then conditionalDrop register

def projectType (program : Program) (type : Term) (projection : Projection) : Check Term := do
  match projection, type with
  | .dereference, .reference _ _ referent => return referent
  | .field index, .tuple fields => getRequired fields[index]? .invalidLayout "tuple projection exceeds runtime shape"
  | .field _, .array element _ | .index _, .array element _ | .dynamicIndex _, .array element _ => return element
  | .variant _, _ => return type
  | .field index, .nominal declaration arguments =>
    let data ← getRequired (program.dataType declaration) .unknownName "unknown field layout"
    let variant ← getRequired data.variants.head? .invalidLayout "nominal type has no variant"
    let field ← getRequired variant.fields[index]? .invalidLayout "nominal field projection exceeds runtime shape"
    let subs ← bindArguments data.generics arguments
    substitute program.limits.normalization subs field.type
  | _, _ => reject .malformedCore "unsupported typed projection at VM boundary"

/-- Physical reads follow the explicit Core ownership operation. Conditional
    initialization flags realize (rather than infer) those same transitions. -/
def lowerPlace (fuel : Nat) (place : Place) (mode : Nat) : EmitM (Nat × Term) := do
  match fuel with
  | 0 => reject .resourceLimit "physical place lowering exhausted"
  | fuel + 1 =>
    let root ← localRegister place.root
    let rec project : Nat → Nat → Term → List Projection → EmitM (Nat × Term)
      | 0, _, _, _ => reject .resourceLimit "physical projection depth exhausted"
      | _, register, type, [] => return (register, type)
      | fuel + 1, register, type, projection :: rest => do
        let program := (← get).global.analyzed.core.source
        let nextType ← projectType program type projection
        if projection matches .variant _ then project fuel register nextType rest else
          let finalMode := if rest.isEmpty then mode else 2
          let residentType := if finalMode < 2 then nextType else
            .reference (if finalMode == 3 then .unique else .shared) .staticRegion nextType
          let destination ← temporary (← global (lowerType program.limits.layout residentType))
          match projection with
          | .dereference => let _ ← emit (.deref finalMode destination register); pure ()
          | .field index | .index index => let _ ← emit (.project finalMode destination register index); pure ()
          | .dynamicIndex _ => reject .missingEvidence "dynamic projection needs the analyzed disjoint-index decision tree"
          | .variant _ => pure ()
          project fuel destination residentType rest
    if place.projections.isEmpty then
      if mode < 2 then return (root.register, root.type) else
        let type := Term.reference (if mode == 3 then .unique else .shared) .staticRegion root.type
        let destination ← temporary (← global (lowerType (← get).global.analyzed.core.source.limits.layout type))
        let _ ← emit (.borrow (mode == 3) false destination root.register)
        return (destination, type)
    else project fuel root.register root.type place.projections

def consumePlace (place : Place) : EmitM Unit := do
  if place.projections.isEmpty then setFlag (← localRegister place.root) false

def initialized (destination : Id) : EmitM Unit := setFlag (← localRegister destination) true

def lowerConstant (fuel : Nat) (destination : Nat) (type : Term) (constant : Term) : EmitM Unit := do
  match fuel with
  | 0 => reject .resourceLimit "constant lowering exhausted"
  | fuel + 1 =>
    match constant with
    | .constant value => let _ ← emit (.constant destination (← global (internConstant (.scalar value)))); pure ()
    | .constantTuple [] => let _ ← emit (.constant destination (← global (internConstant .unit))); pure ()
    | .constantTuple fields =>
      let .tuple types := type | reject .typeMismatch "structural tuple constant type differs"
      let registers ← (types.zip fields).mapM fun (type, field) => do
        let register ← temporary (← global (lowerType fuel type))
        lowerConstant fuel register type field
        pure register
      let _ ← emit (.construct destination (← global (lowerType fuel type)) none registers)
      pure ()
    | .constantConstructor declaration arguments fields =>
      let program := (← get).global.analyzed.core.source
      let (data, variant) ← getRequired (program.constructor declaration) .unknownName "constant constructor is absent"
      let subs ← bindArguments data.generics arguments
      let types ← variant.fields.mapM (fun f => substitute fuel subs f.type)
      let registers ← (types.zip fields).mapM fun (type, field) => do
        let register ← temporary (← global (lowerType fuel type))
        lowerConstant fuel register type field
        pure register
      let tag := if data.isEnum then data.variants.findIdx? (fun v => v.header.id == declaration) else none
      let _ ← emit (.construct destination (← global (lowerType fuel type)) tag registers)
      pure ()
    | .label .. | .environment .. | .available .. =>
      let _ ← emit (.constant destination (← global (internConstant .unit)))
      pure ()
    | _ => reject .malformedCore "nonstructural runtime constant"

def lowerPatternBindings (fuel : Nat) (subject : Place) (pattern : CheckedPattern)
    (bindings : List PatternBinding) : EmitM Unit := do
  for binding in bindings do
    let exists := (← get).locals.any (fun local => local.source == binding.slot.id)
    let destination ← if exists then localRegister binding.slot.id else allocateRegister binding.slot
    let source := { subject with projections := subject.projections ++ binding.projections }
    let mode := match binding.borrowed with | none => 1 | some (.shared, _) => 2 | some (.unique, _) => 3
    let (register, _) ← lowerPlace fuel source mode
    let _ ← emit (.move destination.register register)
    consumePlace source
    setFlag destination true
  match pattern with
  | .binder .. => pure ()
  | .wildcard _ => conditionalDrop (← localRegister subject.root)
  | .constructor _ (.reference _) _ => conditionalDrop (← localRegister subject.root)
  | .constructor .. =>
    let source ← localRegister subject.root
    let _ ← emit (.deconstruct source.register)
    setFlag source false

def testPattern (fuel : Nat) (subject : Place) (pattern : CheckedPattern) : EmitM (List Nat) := do
  match fuel with
  | 0 => reject .resourceLimit "structural decision lowering exhausted"
  | fuel + 1 =>
    match pattern with
    | .wildcard _ | .binder .. => return []
    | .constructor type key fields =>
      let (register, _) ← lowerPlace fuel subject 0
      let own ← match key with
        | .constructor declaration => do
          let program := (← get).global.analyzed.core.source
          let (data, _) ← getRequired (program.constructor declaration) .unknownName "pattern constructor is absent"
          if !data.isEnum then pure [] else
            let index ← getRequired (data.variants.findIdx? (fun v => v.header.id == declaration)) .malformedCore "enum variant is absent"
            let discriminant ← temporary 4
            let _ ← emit (.enumTag discriminant register)
            let constant ← global (internConstant (.scalar (.integer false .w32 (Int.ofNat index))))
            let branch ← emit (.nop)
            let success := (← get).code.length
            patch branch (.switch discriminant [(constant, success)] 0)
            pure [branch]
        | .scalar scalar => do
          let expected ← temporary (← global (lowerType fuel (scalarValueType scalar)))
          let _ ← emit (.constant expected (← global (internConstant (.scalar scalar))))
          let discriminant ← temporary 4
          let op := match scalar with | .character _ => "IntEq" | _ => "IntEq"
          let _ ← emit (.primitive discriminant op [register, expected])
          let one ← global (internConstant (.scalar (.integer false .w32 1)))
          let branch ← emit (.nop)
          patch branch (.switch discriminant [(one, (← get).code.length)] 0)
          pure [branch]
        | _ => pure []
      let children ← fields.zipIdx |>.mapM fun (field, index) =>
        let projection := match key with | .reference _ => Projection.dereference | _ => .field index
        testPattern fuel { subject with projections := subject.projections ++ [projection] } field
      return own ++ children.flatten

def patchFailure (branches : List Nat) (failure : Nat) : EmitM Unit := do
  for branch in branches do
    let instruction ← getRequired (← get).code[branch]? .malformedCore "missing pattern branch instruction"
    match instruction with
    | .switch discriminant cases _ => patch branch (.switch discriminant cases failure)
    | _ => reject .malformedCore "pattern failure patch targets a non-branch"

def registerSignature (type : Term) : EmitM Signature := do
  let program := (← get).global.analyzed.core
  let (signature, _) ← (callableSignature program.source type).run program.inference
  return signature

mutual
  def lowerCore (fuel : Nat) (core : Core) (destination : Option RegisterInfo)
      (onReturn : EmitM Unit) : EmitM Unit := do
    match fuel with
    | 0 => reject .resourceLimit "VM control lowering exhausted"
    | fuel + 1 =>
      match core with
      | .result place =>
        let (register, _) ← lowerPlace fuel place 1
        consumePlace place
        match destination with
        | some destination =>
          let _ ← emit (.move destination.register register)
          setFlag destination true
          onReturn
        | none =>
          cleanupRegisters (← get).locals [register]
          let _ ← emit (.ret (some register))
          pure ()
      | .step operation next => lowerOperation fuel operation; lowerCore fuel next destination onReturn
      | .bind slot computation next =>
        let result ← allocateRegister slot
        lowerCore fuel computation (some result) (lowerCore fuel next destination onReturn)
      | .scoped _ body =>
        let entry := (← get).locals.map (·.source)
        lowerCore fuel body destination (do
          let ending := (← get).locals.filter (fun local => !entry.contains local.source)
          cleanupRegisters ending (destination.toList.map (·.register))
          onReturn)
      | .cases subject clauses =>
        let rec cases : List CoreCase → EmitM Unit
          | [] => let _ ← emit .unreachable; pure ()
          | .clause pattern bindings body :: rest => do
            let tests ← testPattern fuel subject pattern
            lowerPatternBindings fuel subject pattern bindings
            lowerCore fuel body destination onReturn
            let failure := (← get).code.length
            patchFailure tests failure
            cases rest
        cases clauses
      | .label _ brand _ type body =>
        let state ← get
        let slot := state.nextLabel
        let result ← temporary (← global (lowerType fuel type))
        modify fun s => { s with nextLabel := s.nextLabel + 1, labels := (brand, slot, result) :: s.labels,
          global.artifact.requiredFeatures := Nat.lor s.global.artifact.requiredFeatures 4 }
        let start ← emit (.nop)
        let before := (← get).locals
        let info : RegisterInfo := ⟨0, result, type, ← temporary 4⟩
        lowerCore fuel body (some info) (do let _ ← emit (.labelPop slot); pure ())
        let target := (← get).code.length
        patch start (.labelPush slot result target)
        setFlag info true
        modify fun s => { s with labels := s.labels.filter (fun (b, _, _) => b != brand) }
        match destination with
        | some destination =>
          let _ ← emit (.move destination.register result)
          setFlag destination true
          onReturn
        | none =>
          cleanupRegisters (← get).locals [result]
          let _ ← emit (.ret (some result))
          pure ()
      | .leave brand payload =>
        let (_, slot, _) ← getRequired ((← get).labels.find? (fun (b, _, _) => b == brand)) .tail "label destination was not control-fused before lowering"
        let (value, _) ← lowerPlace fuel payload 1
        consumePlace payload
        let _ ← emit (.leave slot value)
        pure ()
      | .tail call => lowerInvocation fuel none call true
      | .fatal reason =>
        let _ ← emit (.abort (some (toString (repr reason))))
        pure ()
      | .handle identity body clauses => lowerHandler fuel identity body clauses destination onReturn

  def lowerOperation (fuel : Nat) (operation : CoreOp) : EmitM Unit := do
    let program := (← get).global.analyzed.core
    match operation with
    | .declare slot => let _ ← allocateRegister slot; pure ()
    | .constant destination value =>
      let destination ← localRegister destination
      lowerConstant fuel destination.register destination.type value
      setFlag destination true
    | .literalView destination binding bytes =>
      let destination ← localRegister destination
      let constant ← global (internConstant (.staticData binding.localId 1 bytes))
      let _ ← emit (.constant destination.register constant)
      setFlag destination true
    | .read destination source forced =>
      let destination ← localRegister destination
      let capability ← deriveUse program.source program.inference destination.type
      let move := forced || capability != .duplicable
      let (register, _) ← lowerPlace fuel source (if move then 1 else 0)
      let _ ← emit (if move then .move destination.register register else .copy destination.register register)
      if move then consumePlace source
      setFlag destination true
    | .initialize destination source | .assign destination source =>
      let (register, _) ← lowerPlace fuel source 1
      consumePlace source
      if destination.projections.isEmpty then
        let destination ← localRegister destination.root
        if operation matches .assign .. then conditionalDrop destination
        let _ ← emit (.move destination.register register)
        setFlag destination true
      else
        let (address, _) ← lowerPlace fuel destination 3
        let _ ← emit (.store address register)
        let _ ← emit (.endBorrow address)
        pure ()
    | .construct destination declaration fields =>
      let output ← localRegister destination
      let registers ← fields.mapM (fun place => return (← lowerPlace fuel place 1).1)
      for place in fields do consumePlace place
      let tag ← match declaration with
        | none => pure none
        | some declaration => do
          let (data, _) ← getRequired (program.source.constructor declaration) .unknownName "unknown constructed variant"
          pure (if data.isEnum then data.variants.findIdx? (fun v => v.header.id == declaration) else none)
      let _ ← emit (.construct output.register (← global (lowerType fuel output.type)) tag registers)
      setFlag output true
    | .closure destination function arguments captures _ =>
      let output ← localRegister destination
      let registers ← captures.mapM fun capture => do
        let mode := match capture.mode with | .owned => 1 | .shared => 2 | .unique => 3
        let (register, _) ← lowerPlace fuel capture.source mode
        if mode == 1 then consumePlace capture.source
        pure register
      let function ← global (ensureCallableFunction fuel function arguments)
      let _ ← emit (.makeCallable output.register (← global (lowerType fuel output.type)) function registers)
      setFlag output true
    | .borrow destination mode _ source =>
      let output ← localRegister destination
      let (register, _) ← lowerPlace fuel source (if mode == .unique then 3 else 2)
      let _ ← emit (.move output.register register)
      setFlag output true
    | .endLoan identity =>
      let reference ← localRegister identity
      let _ ← emit (.endBorrow reference.register)
      setFlag reference false
    | .discard source =>
      if source.projections.isEmpty then conditionalDrop (← localRegister source.root)
      else
        let (register, _) ← lowerPlace fuel source 1
        let _ ← emit (.drop register)
        pure ()
    | .deconstruct source pattern bindings => lowerPatternBindings fuel source pattern bindings
    | .invoke destination call => lowerInvocation fuel (some (← localRegister destination)) call false
    | .perform destination operation effectInstance payload signature =>
      let (effect, _) ← getRequired (program.source.operation operation) .unknownName "unknown performed operation"
      let protocol ← global (lowerProtocol fuel (.effect effect.header.id effectInstance))
      let operation ← getRequired (effect.operations.findIdx? (fun op => op.header.id == operation)) .malformedCore "operation not in its effect family"
      let registers ← payload.mapM (fun value => return (← lowerPlace fuel value 1).1)
      for value in payload do consumePlace value
      let output ← localRegister destination
      let _ ← emit (.perform (if signature.output == .bottom then none else some output.register) protocol operation registers)
      if signature.output != .bottom then setFlag output true
    | .machine destination binding arguments signature permission =>
      require (!signature.unsafeCall || permission) .unsafeOperation "unsafe leaf lacks permission"
      let registers ← arguments.mapM (fun value => return (← lowerPlace fuel value 1).1)
      for value in arguments do consumePlace value
      let output ← localRegister destination
      let import ← getRequired (program.source.imports.find? (fun i => i.identity == binding)) .missingImport "unadmitted machine leaf"
      if let some operation := import.primitive then
        let _ ← emit (.primitive output.register operation registers)
        pure ()
      else
        let import ← global (lowerImport fuel binding)
        let _ ← emit (.hostCall (some output.register) import registers)
        pure ()
      setFlag output true
    | .seal _ => pure ()
    | .test destination subject pattern _ _ =>
      let output ← localRegister destination
      let failures ← testPattern fuel subject pattern
      let _ ← emit (.construct output.register (← global (lowerType fuel output.type)) (some 0) [])
      let skip ← emit .nop
      let failure := (← get).code.length
      patchFailure failures failure
      let _ ← emit (.construct output.register (← global (lowerType fuel output.type)) (some 1) [])
      patch skip (.jump (← get).code.length)
      setFlag output true

  def lowerInvocation (fuel : Nat) (destination : Option RegisterInfo) (call : CallSite) (tail : Bool) : EmitM Unit := do
    let (callee, calleeType) ← lowerPlace fuel call.callee 1
    let registers ← call.inputs.mapM (fun input => return (← lowerPlace fuel input.value 1).1)
    for input in call.inputs do consumePlace input.value
    consumePlace call.callee
    let mode := match call.signature.receiver with | none => 0 | some receiver => receiverNumber receiver
    if tail then cleanupRegisters (← get).locals (callee :: registers)
    match calleeType with
    | .continuation _ _ _ _ =>
      require (registers.length == 1) .malformedCore "resumption has a nonunary payload"
      let value := registers.headD 0
      if tail then let _ ← emit (.tailResume callee mode value); pure ()
      else
        let output ← getRequired destination .malformedCore "resumption call has no result destination"
        let _ ← emit (.resume output.register callee mode value)
        setFlag output true
    | .callable declaration arguments =>
      let program := (← get).global.analyzed.core.source
      if let some (effect, operation) := program.operation declaration then
        let protocol ← global (lowerProtocol fuel (.effect effect.header.id (arguments.take effect.generics.length)))
        let index ← getRequired (effect.operations.findIdx? (fun op => op.header.id == operation.header.id)) .malformedCore "missing operation index"
        let _ ← emit (.perform (destination.map (·.register)) protocol index registers)
        if let some output := destination then setFlag output true
      else if let some function := program.function declaration then
        if let some binding := function.runtimeBinding then
          let import ← getRequired (program.imports.find? (fun i => i.identity == binding)) .missingImport "runtime leaf binding is absent"
          if let some operation := import.primitive then
            let output ← getRequired destination .tail "machine primitive cannot directly realize a proper tail invocation"
            let _ ← emit (.primitive output.register operation registers)
            setFlag output true
          else
            require (!tail) .tail "foreign or host tail transfer lacks an admitted constant-space convention"
            let _ ← emit (.hostCall (destination.map (·.register)) (← global (lowerImport fuel binding)) registers)
            if let some output := destination then setFlag output true
        else
          if tail then let _ ← emit (.tailIndirect callee mode registers); pure ()
          else
            let _ ← emit (.indirect (destination.map (·.register)) callee mode registers)
            if let some output := destination then setFlag output true
      else
        if tail then let _ ← emit (.tailIndirect callee mode registers); pure ()
        else
          let _ ← emit (.indirect (destination.map (·.register)) callee mode registers)
          if let some output := destination then setFlag output true
    | _ =>
      if tail then let _ ← emit (.tailIndirect callee mode registers); pure ()
      else
        let _ ← emit (.indirect (destination.map (·.register)) callee mode registers)
        if let some output := destination then setFlag output true

  def lowerHandler (fuel identity : Nat) (body : Core) (clauses : List CoreHandler)
      (destination : Option RegisterInfo) (onReturn : EmitM Unit) : EmitM Unit := do
    let state ← get
    let program := state.global.analyzed.core
    let outputType := destination.map (·.type) |>.getD state.function.signature.output
    let dependencies := (← coreInputs fuel (.handle identity body clauses)).map (·.root) |>.eraseDups
    let captures ← dependencies.mapM fun id => do
      let local ← localRegister id
      return (⟨⟨id, []⟩, .shared, id, local.type⟩ : Capture)
    let bodyFunction ← liftBody fuel body outputType captures []
    let operationClauses := clauses.filterMap fun clause => match clause with
      | .operation op args patterns bindings continuation policy body => some (op, args, patterns, bindings, continuation, policy, body)
      | _ => none
    let lifted ← operationClauses.mapM fun (operation, effectInstance, patterns, bindings, continuation, policy, body) => do
      let parameters := bindings.map (·.slot) ++ continuation.toList
      let function ← liftBody fuel body outputType captures parameters
      let (effect, _) ← getRequired (program.source.operation operation) .unknownName "handler operation is absent"
      let protocol ← global (lowerProtocol fuel (.effect effect.header.id effectInstance))
      let operation ← getRequired (effect.operations.findIdx? (fun op => op.header.id == operation)) .malformedCore "handler operation index is absent"
      let signature ← global (lowerSignature fuel { arguments := parameters.map (·.type), output := outputType })
      let resumption ← continuation.mapM (fun slot => global (lowerType fuel slot.type))
      return (function, (⟨protocol, operation, signature, resumption⟩ : VM.HandlerClause))
    let definition := (← get).global.artifact.handlers.length
    let result ← global (lowerType fuel outputType)
    modify fun state => { state with global.artifact.handlers := state.global.artifact.handlers ++
      [⟨result, lifted.map Prod.snd, true⟩],
      global.artifact.requiredFeatures := Nat.lor state.global.artifact.requiredFeatures 8 }
    let handlerType := (← get).global.artifact.types.length
    let captureType ← global (lowerType fuel (.tuple (captures.map captureResidentType)))
    modify fun state => { state with global.artifact.types := state.global.artifact.types ++
      [.handler definition captureType s!"handler#{identity}"] }
    let handler ← temporary handlerType
    let _ ← emit (.makeHandler handler definition (lifted.map Prod.fst))
    let resultRegister ← match destination with | some value => pure value.register | none => temporary result
    let _ ← emit (.handle resultRegister handler bodyFunction [])
    match destination with
    | some destination => setFlag destination true; onReturn
    | none => let _ ← emit (.ret (some resultRegister)); pure ()

  def liftBody (fuel : Nat) (body : Core) (output : Term) (captures : List Capture)
      (parameters : List TypedSlot) : EmitM Nat := do
    let state ← get
    let identity : DeclId := ⟨state.function.declaration.packageId, state.global.nextSynthetic⟩
    let signature : Signature := { arguments := parameters.map (·.type), output,
      effects := state.function.signature.effects, receiver := some .shared }
    let function : CoreFunction := ⟨identity, signature, parameters, captures, .shared, body, none, state.function.span⟩
    let index := state.global.functionIds.length
    modify fun state => { state with global.nextSynthetic := state.global.nextSynthetic + 1,
      global.pending := state.global.pending ++ [function],
      global.functionIds := state.global.functionIds ++ [(identity, index)],
      global.analyzed.core.functions := state.global.analyzed.core.functions ++ [function] }
    let captureRegisters ← captures.mapM (fun capture => return (← lowerPlace fuel capture.source 2).1)
    let captureType ← global (lowerType fuel (.tuple (captures.map captureResidentType)))
    let vmSignature ← global (lowerSignature fuel signature)
    let type := (← get).global.artifact.types.length
    modify fun state => { state with global.artifact.types := state.global.artifact.types ++
      [.callable vmSignature captureType 0 (declarationName identity) true true] }
    let register ← temporary type
    let _ ← emit (.makeCallable register type index captureRegisters)
    return register

  def ensureCallableFunction (fuel : Nat) (declaration : DeclId) (arguments : List Term) : LowerM Nat := do
    let state ← get
    if let some index := lookup declaration state.functionIds then return index
    match fuel with
    | 0 => reject .resourceLimit "callable wrapper lowering exhausted"
    | fuel + 1 =>
      let program := state.analyzed.core.source
      let (signature, binders) ← declarationSignature program declaration
      let subs ← bindArguments binders arguments
      let signature ← substituteSignature fuel subs signature
      let parameters := signature.arguments.zipIdx |>.map fun (type, index) =>
        (⟨state.nextSynthetic + index + 1, type, false, {}⟩ : TypedSlot)
      let result : TypedSlot := ⟨state.nextSynthetic + parameters.length + 1, signature.output, false, {}⟩
      let places := parameters.map (fun p => (⟨p.id, []⟩ : Place))
      let operation ← if let some _ := program.constructor declaration then
          pure (CoreOp.construct result.id (some declaration) places)
        else if let some (effect, _) := program.operation declaration then
          pure (.perform result.id declaration (arguments.take effect.generics.length) places signature)
        else
          let function ← getRequired (program.function declaration) .missingEvidence "missing callable declaration"
          let binding ← getRequired function.runtimeBinding .missingEvidence "missing callable body"
          pure (.machine result.id binding places signature signature.unsafeCall)
      let body := Core.step (.declare result) (.step operation (.result ⟨result.id, []⟩))
      let function : CoreFunction := ⟨declaration, signature, parameters, [], .shared, body, none, {}⟩
      let index := state.functionIds.length
      set { state with functionIds := state.functionIds ++ [(declaration, index)], pending := state.pending ++ [function],
        nextSynthetic := state.nextSynthetic + parameters.length + 2 }
      return index

  def lowerImport (fuel : Nat) (identity : DeclId) : LowerM Nat := do
    let state ← get
    if let some index := lookup identity state.importIds then return index
    let binding ← getRequired (state.analyzed.core.source.imports.find? (fun i => i.identity == identity)) .missingImport "runtime import is not admitted"
    let signature ← lowerSignature fuel binding.signature
    let index := (← get).artifact.imports.length
    modify fun state => { state with importIds := state.importIds ++ [(identity, index)],
      artifact.imports := state.artifact.imports ++ [⟨binding.capability.getD "", binding.symbol, signature, true⟩],
      artifact.requiredFeatures := Nat.lor state.artifact.requiredFeatures 32 }
    return index
end

def lowerFunction (function : CoreFunction) : LowerM Unit := do
  let state ← get
  let signature ← lowerSignature state.analyzed.core.source.limits.layout function.signature
  let captureType ← lowerType state.analyzed.core.source.limits.layout (.tuple (function.captures.map captureResidentType))
  let state ← get
  let initial : FunctionLowering := { global := state, function,
    registers := [if function.captures.isEmpty then 0 else captureType] }
  let action : EmitM Unit := do
    for parameter in function.parameters do let _ ← allocateRegister parameter true; pure ()
    for (capture, index) in function.captures.zipIdx do
      let type := captureResidentType capture
      let slot : TypedSlot := ⟨capture.parameter, type, capture.mode == .unique, function.span⟩
      let register ← allocateRegister slot
      let _ ← emit (.project (if function.receiver == .owned then 1 else 0) register.register 0 index)
      setFlag register true
    lowerCore state.analyzed.core.source.limits.elaboration function.body none (pure ())
  let (_, emitted) ← action.run initial
  let start := emitted.global.artifact.code.length
  let flags := if function.signature.output == .bottom then 4 else 0
  let vmFunction : VM.Function := ⟨declarationName function.declaration, flags, signature,
    if function.captures.isEmpty then none else some (receiverNumber function.receiver),
    emitted.registers, start, emitted.code.length, emitted.nextLabel⟩
  set { emitted.global with artifact.functions := emitted.global.artifact.functions ++ [vmFunction],
    artifact.code := emitted.global.artifact.code ++ emitted.code }

def lowerProgram (program : AnalyzedProgram) (entry : DeclId) : Check VM.Artifact := do
  let functions := program.core.functions
  let initial : Lowering := { analyzed := program,
    artifact := { entry := functions.findIdx? (fun f => f.declaration == entry), types := builtinTypes },
    functionIds := functions.zipIdx |>.map (fun (function, index) => (function.declaration, index)),
    pending := functions }
  let rec emitPending : Nat → LowerM Unit
    | 0 => reject .resourceLimit "VM emission worklist exhausted"
    | fuel + 1 => do
      let state ← get
      match state.pending with
      | [] => pure ()
      | function :: rest =>
        set { state with pending := rest }
        lowerFunction function
        emitPending fuel
  let (_, result) ← (emitPending program.core.source.limits.solving).run initial
  require result.artifact.entry.isSome .unknownName "entry function has no emitted specialization"
  return result.artifact

end Glorious.Semantics
