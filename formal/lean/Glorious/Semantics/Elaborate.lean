import Glorious.Semantics.Scalar

namespace Glorious.Semantics

structure Local where
  id : Id
  name : String
  type : Term
  mutable : Bool
  closureDepth : Nat
  deriving Repr

structure Elaboration where
  program : Program
  bindings : List Binding
  module : ModuleId
  inference : Inference := {}
  nextId : Id := 1
  locals : List Local := []
  labelNames : List (String × Term) := []
  functions : List CoreFunction := []
  captures : List Capture := []
  closureDepth : Nat := 0
  unsafePermission : Bool := false
  effectContexts : List (List Term) := []
  permittedEffects : Term := .row [] []
  deriving Repr

abbrev ElabM := StateT Elaboration Check

def infer (action : InferM α) : ElabM α := do
  let state ← get
  let (result, inference) ← action.run state.inference
  set { state with inference }
  return result

def newId : ElabM Id := do
  let state ← get
  set { state with nextId := state.nextId + 1 }
  return state.nextId

def newSlot (type : Term) (span : Span := {}) (mutable : Bool := false) : ElabM TypedSlot := do
  return ⟨← newId, type, mutable, span⟩

structure Elaborated where
  type : Term
  code : Core
  deriving Repr

def produce (type : Term) (span : Span) (operation : Id → CoreOp) : ElabM Elaborated := do
  let slot ← newSlot type span
  return ⟨type, .step (.declare slot) (.step (operation slot.id) (.result ⟨slot.id, []⟩))⟩

def bindExpressions (values : List Elaborated) (continuation : List TypedSlot → Core) : ElabM Core := do
  let slots ← values.mapM (fun value => newSlot value.type)
  return (values.zip slots).foldr (fun (value, slot) next => .bind slot value.code next) (continuation slots)

def ensureExpected (actual : Term) (expected : Option Term) : ElabM Unit := do
  match expected with
  | none => pure ()
  | some expected => infer (subtype (← get).program actual expected)

def resolveTerm (program : Program) (bindings : List Binding) (module : ModuleId) : Nat → Term → Check Term
  | 0, _ => reject .resourceLimit "type-name resolution exhausted"
  | fuel + 1, term => do
    match term with
    | .named path arguments kind =>
      let namespace := match kind with | .effect => .effect | .constant => .value | _ => .type
      let binding ← resolve program bindings module namespace ⟨path⟩
      let arguments ← arguments.mapM (resolveTerm program bindings module fuel)
      if kind == .effect then return .effect binding.declaration arguments
      if kind == .constant then
        let constant ← getRequired (program.constants.find? (fun c => c.header.id == binding.declaration)) .typeMismatch "constant parameter is not structural"
        let subs ← bindArguments constant.generics arguments
        return ← substitute fuel subs constant.value
      if program.aliases.any (fun a => a.header.id == binding.declaration) then return .alias binding.declaration arguments
      return .nominal binding.declaration arguments
    | _ => term.mapChildrenM (resolveTerm program bindings module fuel)

def resolveConstraint (program : Program) (bindings : List Binding) (module : ModuleId)
    (fuel : Nat) (constraint : Constraint) : Check Constraint := do
  let resolveT := resolveTerm program bindings module fuel
  match constraint with
  | .named path arguments negative =>
    let binding ← resolve program bindings module .trait ⟨path⟩
    return .implements binding.declaration (← arguments.mapM resolveT) negative
  | .equal a b => return .equal (← resolveT a) (← resolveT b)
  | .outlives a b => return .outlives (← resolveT a) (← resolveT b)
  | .rowIncludes a b => return .rowIncludes (← resolveT a) (← resolveT b)
  | .implements d args n => return .implements d (← args.mapM resolveT) n
  | .use t q => return .use (← resolveT t) q
  | .callable r a o e u => return .callable (← resolveT r) (← resolveT a) (← resolveT o) (← resolveT e) u
  | .runsIn r a args after u => return .runsIn (← resolveT r) (← resolveT a) (← resolveT args) (← resolveT after) u
  | .higherRanked binders requirements =>
    match fuel with
    | 0 => reject .resourceLimit "higher-ranked name resolution exhausted"
    | n + 1 => return .higherRanked binders (← requirements.mapM (resolveConstraint program bindings module n))

def resolveSignature (program : Program) (bindings : List Binding) (module : ModuleId)
    (signature : Signature) : Check Signature := do
  let fuel := program.limits.normalization
  return { signature with
    arguments := ← signature.arguments.mapM (resolveTerm program bindings module fuel)
    output := ← resolveTerm program bindings module fuel signature.output
    effects := ← resolveTerm program bindings module fuel signature.effects
    constraints := ← signature.constraints.mapM (resolveConstraint program bindings module fuel) }

def resolveProgramTerms (program : Program) (bindings : List Binding) : Check Program := do
  let fuel := program.limits.normalization
  let resolveField (field : FieldDecl) : Check FieldDecl := do
    return { field with type := ← resolveTerm program bindings field.header.module fuel field.type }
  let dataTypes ← program.dataTypes.mapM fun data => do
    let variants ← data.variants.mapM fun variant => do
      return { variant with fields := ← variant.fields.mapM resolveField }
    return { data with variants,
      quantityMarker := ← data.quantityMarker.mapM (resolveTerm program bindings data.header.module fuel) }
  let aliases ← program.aliases.mapM fun aliasDecl => do
    return { aliasDecl with value := ← resolveTerm program bindings aliasDecl.header.module fuel aliasDecl.value }
  let functions ← program.functions.mapM fun function => do
    return { function with signature := ← resolveSignature program bindings function.header.module function.signature,
      parameters := ← function.parameters.mapM (fun parameter => do
        return { parameter with type := ← parameter.type.mapM (resolveTerm program bindings function.header.module fuel) }) }
  let constants ← program.constants.mapM fun constant => do
    return { constant with type := ← resolveTerm program bindings constant.header.module fuel constant.type,
      value := ← resolveTerm program bindings constant.header.module fuel constant.value }
  let effects ← program.effects.mapM fun effect => do
    return { effect with requirements := ← effect.requirements.mapM (resolveConstraint program bindings effect.header.module fuel),
      operations := ← effect.operations.mapM (fun operation => do
        return { operation with signature := ← resolveSignature program bindings operation.header.module operation.signature }) }
  let traits ← program.traits.mapM fun trait => do
    return { trait with supertraits := ← trait.supertraits.mapM (resolveConstraint program bindings trait.header.module fuel),
      members := ← trait.members.mapM (fun member => do
        return { member with defaultValue := ← member.defaultValue.mapM (resolveTerm program bindings trait.header.module fuel),
          signature := ← member.signature.mapM (resolveSignature program bindings trait.header.module) }) }
  let implementations ← program.implementations.mapM fun implementation => do
    return { implementation with
      arguments := ← implementation.arguments.mapM (resolveTerm program bindings implementation.header.module fuel),
      requirements := ← implementation.requirements.mapM (resolveConstraint program bindings implementation.header.module fuel),
      associated := ← implementation.associated.mapM (fun (member, value) => do
        return (member, ← resolveTerm program bindings implementation.header.module fuel value)) }
  return { program with dataTypes, aliases, functions, constants, effects, traits, implementations }

def captureRank : CaptureMode → Nat | .shared => 0 | .unique => 1 | .owned => 2

def requestCapture (place : Place) (type : Term) (mode : CaptureMode) : ElabM Unit := do
  let state ← get
  let local := state.locals.find? (fun local => local.id == place.root)
  match local with
  | none => pure ()
  | some local =>
    if local.closureDepth ≥ state.closureDepth then return
    let enclosing := state.captures.find? (fun capture => capture.source.root == place.root &&
      capture.source.projections.isPrefixOf place.projections)
    match enclosing with
    | some capture =>
      modify fun state => { state with captures := state.captures.map fun current =>
        if current.parameter == capture.parameter && captureRank current.mode < captureRank mode
        then { current with mode } else current }
    | none =>
      let parameter ← newId
      let nested := state.captures.filter (fun c => c.source.root == place.root && place.projections.isPrefixOf c.source.projections)
      let mode := nested.foldl (fun mode c => if captureRank c.mode > captureRank mode then c.mode else mode) mode
      modify fun state => { state with captures := state.captures.filter
          (fun c => !(c.source.root == place.root && place.projections.isPrefixOf c.source.projections)) ++
        [⟨place, mode, parameter, type⟩] }

def mapCoreOpPlaces (f : Place → Place) : CoreOp → CoreOp
  | .read dst src force => .read dst (f src) force
  | .initialize dst src => .initialize (f dst) (f src)
  | .assign dst src => .assign (f dst) (f src)
  | .construct dst constructor fields => .construct dst constructor (fields.map f)
  | .closure dst function arguments captures materialized => .closure dst function arguments
      (captures.map fun c => { c with source := f c.source }) materialized
  | .borrow dst mode region src => .borrow dst mode region (f src)
  | .discard src => .discard (f src)
  | .invoke dst call => .invoke dst { call with callee := f call.callee,
      inputs := call.inputs.map (fun input => { input with value := f input.value }) }
  | .perform dst op args payload sig => .perform dst op args (payload.map f) sig
  | .deconstruct src pattern bindings => .deconstruct (f src) pattern bindings
  | .test dst src pattern positive negative => .test dst (f src) pattern positive negative
  | .machine dst binding args sig permission => .machine dst binding (args.map f) sig permission
  | .seal values => .seal (values.map f)
  | operation => operation

def mapCorePlaces (fuel : Nat) (f : Place → Place) (core : Core) : Check Core :=
  match fuel with
  | 0 => reject .resourceLimit "typed capture transformation exhausted"
  | fuel + 1 =>
    match core with
    | .result value => return .result (f value)
    | .step operation next => return .step (mapCoreOpPlaces f operation) (← mapCorePlaces fuel f next)
    | .bind destination computation next => return .bind destination (← mapCorePlaces fuel f computation) (← mapCorePlaces fuel f next)
    | .scoped scope body => return .scoped scope (← mapCorePlaces fuel f body)
    | .cases subject clauses => return .cases (f subject) (← clauses.mapM fun (.clause pattern bindings body) => do
        return .clause pattern bindings (← mapCorePlaces fuel f body))
    | .label id brand region type body => return .label id brand region type (← mapCorePlaces fuel f body)
    | .handle id body clauses => return .handle id (← mapCorePlaces fuel f body) (← clauses.mapM fun clause => do
        match clause with
        | .completion pattern bindings body => return .completion pattern bindings (← mapCorePlaces fuel f body)
        | .operation op effectInstance patterns bindings k policy body =>
          return .operation op effectInstance patterns bindings k policy (← mapCorePlaces fuel f body))
    | .tail call => return .tail { call with callee := f call.callee,
        inputs := call.inputs.map (fun input => { input with value := f input.value }) }
    | .leave brand payload => return .leave brand (f payload)
    | .fatal reason => return .fatal reason

def capturePlace (captures : List Capture) (place : Place) : Place :=
  match captures.find? (fun capture => capture.source.root == place.root && capture.source.projections.isPrefixOf place.projections) with
  | none => place
  | some capture => ⟨capture.parameter,
      (if capture.mode == .owned then [] else [.dereference]) ++
      place.projections.drop capture.source.projections.length⟩

def patternBindings (fuel : Nat) (pattern : CheckedPattern) (path : List Projection := [])
    (borrowed : Option (Mutability × Term) := none) : Check (List PatternBinding) := do
  match fuel with
  | 0 => reject .resourceLimit "pattern projection lowering exhausted"
  | fuel + 1 =>
    match pattern with
    | .wildcard _ => return []
    | .binder identity _ type => return [⟨⟨identity, type, false, {}⟩, path, borrowed⟩]
    | .constructor type key fields =>
      match key, type, fields with
      | .reference mode, .reference _ region _, [field] =>
        patternBindings fuel field (path ++ [.dereference]) (some (mode, region))
      | _, _, _ =>
        let path := match key with | .constructor declaration => path ++ [.variant declaration] | _ => path
        return (← fields.zipIdx |>.mapM fun (field, index) => patternBindings fuel field (path ++ [.field index]) borrowed).flatten

def expectedCallable (expected : Option Term) : ElabM (Option Signature) := do
  match expected with
  | none => return none
  | some type =>
    let state ← get
    match (callableSignature state.program type).run state.inference with
    | .ok (signature, inference) => modify (fun s => { s with inference }); return some signature
    | .error d => if d.problem == .ambiguous || d.problem == .resourceLimit then throw d else return none

def localByName (path : Path) : ElabM (Option Local) := do
  match path.components with
  | [name] => return (← get).locals.find? (fun local => local.name == name)
  | _ => return none

def expressionPlace : Nat → Expr → ElabM (Place × Term)
  | 0, _ => reject .resourceLimit "place elaboration exhausted"
  | _, .local _ identity => do
    let local ← getRequired ((← get).locals.find? (fun l => l.id == identity)) .unknownName "unknown local identity"
    return (⟨identity, []⟩, local.type)
  | fuel + 1, .name span path [] => do
    let local ← getRequired (← localByName path) .typeMismatch "expression does not denote a local place" span
    return (⟨local.id, []⟩, local.type)
  | fuel + 1, .project span value projection => do
    let (place, type) ← expressionPlace fuel value
    let type ← infer (zonk (← get).program type)
    let type ← match projection, type with
      | .dereference, .reference _ _ referent => pure referent
      | .field index, .tuple fields => getRequired fields[index]? .typeMismatch "tuple field is out of bounds" span
      | .index index, .array element (.constant (.integer _ _ length)) => do
        require (index < length.toNat) .invalidPointer "constant array index is out of bounds" span
        pure element
      | .dynamicIndex _, .array element _ => pure element
      | .field index, .nominal declaration arguments => do
        let program := (← get).program
        let data ← getRequired (program.dataType declaration) .unknownName "unknown field owner"
        require (!data.isEnum) .typeMismatch "enum payloads require structural matching, not unchecked projection" span
        let variant ← getRequired data.variants.head? .invalidLayout "record has no fields"
        let field ← getRequired variant.fields[index]? .typeMismatch "record field is out of bounds" span
        require (visible (← get).module field.header) .privacy "field is private" span
        let subs ← bindArguments data.generics arguments
        substitute program.limits.normalization subs field.type
      | _, _ => reject .typeMismatch "projection does not apply to this type" span
    return (⟨place.root, place.projections ++ [projection]⟩, type)
  | _, expression => reject .typeMismatch "expression is not an addressable place" expression.span

def resolveFixity (spelling : String) (isPrefix : Bool) : ElabM Fixity := do
  let state ← get
  let candidates := state.program.fixities.filter fun f => f.module == state.module && f.spelling == spelling &&
    (f.associativity == .prefix) == isPrefix
  match candidates with
  | [fixity] => return fixity
  | [] => reject .unknownName s!"operator has no selected positional fixity: {spelling}"
  | _ => reject .ambiguous s!"conflicting positional fixities: {spelling}"

def declarationExpr (span : Span) (declaration : DeclId) : ElabM Expr := do
  let state ← get
  let binding ← getRequired (state.bindings.find? (fun b => b.declaration == declaration && b.module == state.module))
    .unknownName "operator target is not available in its declaring namespace" span
  return .name span ⟨[binding.name]⟩ []

def groupOperators (fuel : Nat) (parts : List ChainPart) : ElabM Expr := do
  let rec parse (fuel : Nat) (minimum : Nat) (parts : List ChainPart) : ElabM (Expr × List ChainPart) := do
    match fuel with
    | 0 => reject .resourceLimit "operator grouping exhausted"
    | fuel + 1 =>
      let (left, rest) ← match parts with
        | .operand value :: rest => pure (value, rest)
        | .operator spelling span :: rest => do
          let fixity ← resolveFixity spelling true
          let (right, rest) ← parse fuel fixity.precedence rest
          pure (.apply span (← declarationExpr span fixity.target) [right], rest)
        | [] => reject .invalidSource "operator chain is missing an operand"
      let rec suffix (fuel : Nat) (left : Expr) (parts : List ChainPart)
          (prior : Option Fixity) : ElabM (Expr × List ChainPart) := do
        match fuel, parts with
        | 0, _ => reject .resourceLimit "operator grouping exhausted"
        | _, [] => return (left, [])
        | fuel + 1, .operator spelling span :: rest =>
          let fixity ← resolveFixity spelling false
          if fixity.precedence < minimum then return (left, parts)
          match prior with
          | some previous =>
            if previous.precedence == fixity.precedence then
              require (previous.associativity == fixity.associativity && fixity.associativity != .none)
                .ambiguous "equal-precedence operators have incompatible associativity" span
          | none => pure ()
          let nextMinimum := fixity.precedence + (if fixity.associativity == .right then 0 else 1)
          let (right, remaining) ← parse fuel nextMinimum rest
          let combined := Expr.apply span (← declarationExpr span fixity.target) [left, right]
          suffix fuel combined remaining (some fixity)
        | _, _ => reject .invalidSource "adjacent operands have no application or operator"
      suffix fuel left rest none
  let (expression, rest) ← parse fuel 0 parts
  require rest.isEmpty .invalidSource "operator chain was not completely grouped"
  return expression

mutual
  def elaborate (fuel : Nat) (expression : Expr) (expected : Option Term := none) : ElabM Elaborated := do
    match fuel with
    | 0 => reject .resourceLimit "expression elaboration exhausted" expression.span
    | fuel + 1 =>
      let state ← get
      let span := expression.span
      let program := state.program
      match expression with
      | .operatorChain _ parts => elaborate fuel (← groupOperators fuel parts) expected
      | .unit _ => ensureExpected .unit expected; produce .unit span (fun dst => .constant dst (.constantTuple []))
      | .literal _ literal =>
        let selected ← expected.mapM (fun type => infer (zonk program type))
        match literal with
        | .integer magnitude suffix negative =>
          let scalar ← match suffix, selected with
            | some (.integer signed width), _ => pure (.integer signed width)
            | none, some (.scalar (.integer signed width)) => pure (.integer signed width)
            | none, _ => pure (.integer true .w64)
            | _, _ => reject .typeMismatch "integer literal requires an integer type" span
          let value := if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude
          let .integer signed width := scalar | reject .typeMismatch "noninteger literal type"
          require (integerFits program.target signed width value) .invalidScalar "integer literal magnitude is out of range" span
          let type := Term.scalar scalar
          ensureExpected type expected
          produce type span (fun dst => .constant dst (.constant (.integer signed width value)))
        | .decimalFloat negative significand exponent width =>
          let width := width.getD (match selected with | some (.scalar (.floating width)) => width | _ => .w64)
          let bits ← decimalFloatBits program.limits.normalization width negative significand exponent
          let type := Term.scalar (.floating width)
          ensureExpected type expected
          produce type span (fun dst => .constant dst (.constant (.floating width bits)))
        | .character scalar =>
          require (unicodeScalar scalar) .invalidScalar "character literal is not a Unicode scalar" span
          ensureExpected (.scalar .character) expected
          produce (.scalar .character) span (fun dst => .constant dst (.constant (.character scalar)))
        | .text bytes | .bytes bytes =>
          let binding ← selectLiteralBinding expression selected
          ensureExpected binding.signature.output expected
          produce binding.signature.output span (fun dst => .literalView dst binding.identity bytes)
      | .local .. | .project .. =>
        let (place, type) ← expressionPlace fuel expression
        let capability ← deriveUse program (← get).inference type
        requestCapture place type (if capability == .duplicable then .shared else .owned)
        ensureExpected type expected
        produce type span (fun dst => .read dst place false)
      | .name _ path explicit =>
        if let some local ← localByName path then
          return ← elaborate fuel (.local span local.id) expected
        if let [name] := path.components then
          if name.startsWith "@" then
            let type ← getRequired (lookup (name.drop 1 |>.toString) (← get).labelNames) .unknownName "unknown lexical label" span
            ensureExpected type expected
            return ← produce type span (fun dst => .constant dst type)
        let binding ← resolve program state.bindings state.module .value path
        if let some constant := program.constants.find? (fun c => c.header.id == binding.declaration) then
          let subs ← infer (instantiate program constant.generics explicit)
          let type ← substitute fuel subs constant.type
          ensureExpected type expected
          let value ← substitute fuel subs constant.value >>= fun term => infer (zonk program term)
          return ← produce type span (fun dst => .constant dst value)
        let (signature, binders) ← declarationSignature program binding.declaration
        let subs ← infer (instantiate program binders explicit)
        let arguments := binders.map (fun binder => (lookup binder.id subs).getD (.param binder.id binder.kind))
        let signature ← substituteSignature fuel subs signature
        for requirement in signature.constraints do infer (defer requirement)
        let type := Term.callable binding.declaration arguments
        ensureExpected type expected
        produce type span (fun dst => .closure dst binding.declaration arguments [] true)
      | .tuple _ fields | .array _ fields =>
        let expectedTypes := match expected with
          | some (.tuple types) => types.map some
          | some (.array element _) => List.replicate fields.length (some element)
          | _ => List.replicate fields.length none
        require (expectedTypes.length == fields.length) .typeMismatch "aggregate arity differs from its expected type" span
        let values ← (fields.zip expectedTypes).mapM (fun (field, type) => elaborate fuel field type)
        let type ← match expression with
          | .array .. => do
            let element ← match values.head? with | some v => pure v.type | none => infer (freshMeta .type)
            for value in values do infer (unifyTypes program element value.type)
            pure (.array element (.constant (.integer false .pointer (Int.ofNat fields.length))))
          | _ => pure (if fields.isEmpty then .unit else .tuple (values.map (·.type)))
        ensureExpected type expected
        let output ← newSlot type span
        let code ← bindExpressions values fun slots => .step (.declare output)
          (.step (.construct output.id none (slots.map (fun slot => ⟨slot.id, []⟩))) (.result ⟨output.id, []⟩))
        return ⟨type, code⟩
      | .construct _ declaration arguments fields => elaborateConstructor fuel span declaration arguments fields expected
      | .record _ path arguments fields =>
        let binding ← resolve program state.bindings state.module .value path
        let (_, variant) ← getRequired (program.constructor binding.declaration) .unknownName "record expression names no constructor" span
        let numbered ← fields.mapM fun (name, value) => do
          let index ← getRequired (variant.fields.findIdx? (fun f => f.header.name == name)) .unknownName "unknown constructor field" span
          pure (index, value)
        elaborateConstructor fuel span binding.declaration arguments numbered expected
      | .apply _ callee arguments => elaborateCall fuel span callee arguments expected false
      | .tail _ callee arguments => elaborateCall fuel span callee arguments expected true
      | .borrow _ mode value =>
        let (place, type) ← expressionPlace fuel value
        requestCapture place type (if mode == .shared then .shared else .unique)
        let region ← match expected with
          | some (.reference _ region _) => pure region
          | _ => infer (freshMeta .region)
        let result := Term.reference mode region type
        ensureExpected result expected
        produce result span (fun dst => .borrow dst mode region place)
      | .move _ value =>
        let (place, type) ← expressionPlace fuel value
        requestCapture place type .owned
        ensureExpected type expected
        produce type span (fun dst => .read dst place true)
      | .block _ statements result =>
        let context ← expectedCallable expected
        if context.isSome then
          let identity : DeclId := ⟨state.module.packageId, ← newId⟩
          return ← elaborateLambda fuel span identity [] none none expression [] expected false
        let before := (← get).locals
        let scope ← newId
        let value ← elaborateBlock fuel statements result expected
        modify fun s => { s with locals := before }
        return { value with code := .scoped scope value.code }
      | .lambda _ identity parameters output effects body moves =>
        elaborateLambda fuel span identity parameters output effects body moves expected true
      | .patternCallable _ identity clauses =>
        elaboratePatternCallable fuel span identity clauses expected
      | .unsafeScope _ body =>
        let previous := (← get).unsafePermission
        modify fun s => { s with unsafePermission := true }
        let value ← elaborate fuel body expected
        modify fun s => { s with unsafePermission := previous }
        return value
      | .label _ identity name output body =>
        let output ← match output.or expected with | some t => pure t | none => infer (freshMeta .type)
        let brand := Term.rigid identity .brand ((← get).inference.level + 1)
        let region := Term.rigid identity .region ((← get).inference.level + 1)
        let labelType := Term.label brand region output
        let prior := (← get).labelNames
        modify fun s => { s with labelNames := (name, labelType) :: s.labelNames }
        let value ← elaborate fuel body (some output)
        modify fun s => { s with labelNames := prior }
        return ⟨output, .label identity brand region output value.code⟩
      | .test _ subject pattern =>
        let subject ← elaborate fuel subject none
        let checked ← infer (checkPattern program state.bindings state.module none fuel subject.type pattern)
        let positive ← infer (freshRigid .brand)
        let negative ← infer (freshRigid .brand)
        let region ← infer (freshMeta .region)
        let bindings ← patternBindings fuel checked
        let type := Term.bindings positive region (bindings.map (fun b => b.slot.type))
        ensureExpected type expected
        let output ← newSlot type span
        let code ← bindExpressions [subject] fun slots => .step (.declare output)
          (.step (.test output.id ⟨slots[0]!.id, []⟩ checked positive negative) (.result ⟨output.id, []⟩))
        return ⟨type, code⟩
      | .handle _ body clauses => elaborateHandler fuel span body clauses expected

  def selectLiteralBinding (expression : Expr) (expected : Option Term) : ElabM RuntimeImport := do
    let program := (← get).program
    let candidates := program.imports.filter fun binding => binding.kind == .staticData &&
      (match expected with | none => true | some type => type == binding.signature.output)
    match candidates with
    | [binding] => return binding
    | [] => reject .missingImport "literal view has no exact manifest-bound materializer" expression.span
    | _ => reject .ambiguous "literal view materializer is ambiguous without an expected type" expression.span

  def declarationSignature (program : Program) (declaration : DeclId) : Check (Signature × List Binder) := do
    if let some function := program.function declaration then return (function.signature, function.signature.generics)
    if let some (effect, operation) := program.operation declaration then
      let binders := effect.generics ++ operation.signature.generics
      let effectInstance := Term.effect effect.header.id (effect.generics.map (fun b => .param b.id b.kind))
      return ({ operation.signature with generics := binders, effects := .row [effectInstance] [] }, binders)
    if let some (data, variant) := program.constructor declaration then
      return ({ generics := data.generics, arguments := variant.fields.map (·.type),
        output := .nominal data.header.id (data.generics.map (fun b => .param b.id b.kind)) }, data.generics)
    reject .missingEvidence "declaration has no callable contract"

  def elaborateConstructor (fuel : Nat) (span : Span) (declaration : DeclId) (arguments : List Term)
      (fields : List (Nat × Expr)) (expected : Option Term) : ElabM Elaborated := do
    let state ← get
    let (data, variant) ← getRequired (state.program.constructor declaration) .unknownName "unknown constructor" span
    require (unique (fields.map Prod.fst) && fields.length == variant.fields.length) .typeMismatch "constructor must initialize every field exactly once" span
    let subs ← infer (instantiate state.program data.generics arguments)
    let arguments := data.generics.map (fun b => (lookup b.id subs).getD (.param b.id b.kind))
    let type := Term.nominal data.header.id arguments
    ensureExpected type expected
    -- Preserve source expression order even when named fields are written in
    -- a different order from the declared storage layout.
    let values ← fields.mapM fun (index, expression) => do
      let field ← getRequired variant.fields[index]? .unknownName "unknown constructor field" span
      require (visible state.module field.header) .privacy "constructor field is private" span
      elaborate fuel expression (some (← substitute fuel subs field.type))
    let output ← newSlot type span
    let code ← bindExpressions values fun slots =>
      let order := (fields.map Prod.fst).zip slots
      let places := List.range variant.fields.length |>.map fun index =>
        ⟨((lookup index order).getD output).id, []⟩
      .step (.declare output) (.step (.construct output.id (some declaration) places) (.result ⟨output.id, []⟩))
    return ⟨type, code⟩

  def elaborateCall (fuel : Nat) (span : Span) (callee : Expr) (arguments : List Expr)
      (expected : Option Term) (tail : Bool) : ElabM Elaborated := do
    let state ← get
    let callee ← elaborate fuel callee none
    let signature ← infer (callableSignature (← get).program callee.type)
    require (signature.arguments.length == arguments.length) .typeMismatch "call argument tuple arity differs" span
    require (!signature.unsafeCall || state.unsafePermission) .unsafeOperation "unsafe call requires an explicit unsafe scope" span
    for requirement in signature.constraints do infer (defer requirement)
    ensureExpected signature.output expected
    -- Seed independently known argument constraints before contextual bodies.
    let rec seed : List (Expr × Term) → ElabM Unit
      | [] => pure ()
      | (expression, type) :: rest => do
        match expression with
        | .local _ id =>
          if let some local := (← get).locals.find? (fun l => l.id == id) then infer (unifyTypes state.program local.type type)
        | .name _ path [] =>
          if let some local ← localByName path then infer (unifyTypes state.program local.type type)
        | _ => pure ()
        seed rest
    seed (arguments.zip signature.arguments)
    let values ← (arguments.zip signature.arguments).mapM fun (argument, type) => elaborate fuel argument (some type)
    infer (solveRowInclusion (← get).program state.permittedEffects signature.effects)
    let output ← newSlot signature.output span
    let identity ← newId
    let code ← bindExpressions (callee :: values) fun slots =>
      let callee := (slots.headD output)
      let inputs := (slots.drop 1).zipIdx |>.map fun (slot, index) =>
        (⟨.argument index, ⟨slot.id, []⟩, slot.type⟩ : CallInput)
      let call : CallSite := ⟨identity, ⟨callee.id, []⟩, inputs, signature, span, state.unsafePermission⟩
      match callee.type with
      | .label brand _ _ => .leave brand (inputs.headD ⟨.argument 0, ⟨output.id, []⟩, .unit⟩).value
      | _ => if tail then .tail call else .step (.declare output) (.step (.invoke output.id call) (.result ⟨output.id, []⟩))
    return ⟨if tail then .bottom else signature.output, code⟩

  def elaborateBlock (fuel : Nat) (statements : List Statement) (result : Option Expr)
      (expected : Option Term) : ElabM Elaborated := do
    match fuel, statements with
    | 0, _ => reject .resourceLimit "block elaboration exhausted"
    | fuel + 1, [] => elaborate fuel (result.getD (.unit {})) expected
    | fuel + 1, statement :: rest =>
      let state ← get
      match statement with
      | .binding span pattern mutable annotation initializer =>
        let initializer ← elaborate fuel initializer annotation
        let checked ← infer (checkPattern state.program state.bindings state.module none fuel initializer.type pattern)
        let checkedBindings ← patternBindings fuel checked
        let names ← checked.binders fuel
        let locals := names.map fun (id, name, type) => (⟨id, name, type, mutable, state.closureDepth⟩ : Local)
        modify fun state => { state with locals := locals.reverse ++ state.locals }
        let continuation ← elaborateBlock fuel rest result expected
        let bindings := checkedBindings.map (fun b => { b with slot.mutable := mutable })
        let code ← bindExpressions [initializer] fun slots =>
          coreStepList (bindings.map (fun b => .declare b.slot))
            (.step (.deconstruct ⟨slots[0]!.id, []⟩ checked bindings)
              (.step (.seal (bindings.map (fun b => ⟨b.slot.id, []⟩))) continuation.code))
        return { continuation with code }
      | .assign span destination expression =>
        let (place, type) ← expressionPlace fuel destination
        requestCapture place type .unique
        let value ← elaborate fuel expression (some type)
        let continuation ← elaborateBlock fuel rest result expected
        let code ← bindExpressions [value] fun slots => .step (.assign place ⟨slots[0]!.id, []⟩) continuation.code
        return { continuation with code }
      | .discard span expression =>
        let value ← elaborate fuel expression none
        let continuation ← elaborateBlock fuel rest result expected
        let code ← bindExpressions [value] fun slots => .step (.discard ⟨slots[0]!.id, []⟩) continuation.code
        return { continuation with code }

  def elaborateLambda (fuel : Nat) (span : Span) (identity : DeclId) (parameters : List Parameter)
      (output effects : Option Term) (body : Expr) (assertedMoves : List Place)
      (expected : Option Term) (materialized : Bool) : ElabM Elaborated := do
    let outer ← get
    let context ← expectedCallable expected
    let argumentTypes ← if parameters.isEmpty && context.isSome then pure context.get!.arguments else
      parameters.zipIdx |>.mapM fun (parameter, index) => match parameter.type with
        | some type => pure type
        | none => match context.bind (fun signature => signature.arguments[index]?) with
          | some type => pure type | none => infer (freshMeta .type)
    require (parameters.isEmpty || parameters.length == argumentTypes.length) .typeMismatch "lambda parameter arity differs" span
    let parameters ← if parameters.isEmpty then argumentTypes.mapM (fun type => do
        let id ← newId; pure (⟨id, s!"_implicit{id}", some type, false⟩ : Parameter)) else pure parameters
    let resultType ← match output.or (context.map (·.output)) with | some type => pure type | none => pure .unit
    let row := effects.getD ((context.map (·.effects)).getD (.row [] []))
    let signature : Signature := { arguments := argumentTypes, output := resultType, effects := row }
    let explicit := match row with | .row instances _ => instances | _ => []
    let localParameters := (parameters.zip argumentTypes).map fun (parameter, type) =>
      (⟨parameter.id, parameter.name, type, parameter.mutable, outer.closureDepth + 1⟩ : Local)
    modify fun state => { state with locals := localParameters.reverse ++ outer.locals,
      captures := [], closureDepth := outer.closureDepth + 1, unsafePermission := false,
      permittedEffects := row, effectContexts := explicit :: outer.effectContexts }
    let body ← match body with
      | .block _ statements result => elaborateBlock fuel statements result (some resultType)
      | _ => elaborate fuel body (some resultType)
    for place in assertedMoves do
      let local ← getRequired (outer.locals.find? (fun local => local.id == place.root)) .unknownName "owned-capture assertion names no outer place"
      requestCapture place local.type .owned
    let inner ← get
    let captures := inner.captures
    let receiver := if captures.any (fun c => c.mode == .owned &&
      (deriveUse inner.program inner.inference c.type).toOption != some .duplicable) then .owned
      else if captures.any (fun c => c.mode == .unique) then .unique else .shared
    let body ← mapCorePlaces outer.program.limits.elaboration (capturePlace captures) body.code
    let slots := (parameters.zip argumentTypes).map fun (parameter, type) =>
      (⟨parameter.id, type, parameter.mutable, span⟩ : TypedSlot)
    let coreFunction : CoreFunction := ⟨identity, { signature with receiver := some receiver }, slots, captures,
      receiver, body, none, span⟩
    let synthetic : FunctionDecl := ⟨⟨identity, outer.module, s!"lambda#{identity.localId}", .private, span⟩,
      { signature with receiver := some receiver }, parameters, none, none, none⟩
    set { inner with locals := outer.locals, captures := outer.captures, closureDepth := outer.closureDepth,
      unsafePermission := outer.unsafePermission, permittedEffects := outer.permittedEffects,
      effectContexts := outer.effectContexts, functions := inner.functions ++ [coreFunction],
      program.functions := inner.program.functions ++ [synthetic] }
    let type := Term.callable identity []
    ensureExpected type expected
    produce type span (fun dst => .closure dst identity [] captures materialized)

  def elaboratePatternCallable (fuel : Nat) (span : Span) (identity : DeclId)
      (clauses : List PatternClause) (expected : Option Term) : ElabM Elaborated := do
    let state ← get
    let context ← expectedCallable expected
    let signature ← match context with
      | some signature => pure signature
      | none => do pure ({ arguments := [← infer (freshMeta .type)], output := ← infer (freshMeta .type),
          effects := .row [] [] } : Signature)
    let subjectType := if signature.arguments.length == 1 then signature.arguments.headD .unit else .tuple signature.arguments
    let subject ← newSlot subjectType span
    let explicit := match signature.effects with | .row instances _ => instances | _ => []
    modify fun s => { s with captures := [], closureDepth := s.closureDepth + 1,
      unsafePermission := false, permittedEffects := signature.effects,
      effectContexts := explicit :: s.effectContexts }
    let checkedClauses ← clauses.mapM fun (.clause clauseSpan pattern body) => do
      let before := (← get).locals
      let checked ← infer (checkPattern (← get).program state.bindings state.module none fuel subjectType pattern)
      let bindings ← patternBindings fuel checked
      let names ← checked.binders fuel
      modify fun s => { s with locals := names.map (fun (id, name, type) =>
        ⟨id, name, type, false, state.closureDepth + 1⟩) ++ before }
      let body ← elaborate fuel body (some signature.output)
      modify fun s => { s with locals := before }
      return CoreCase.clause checked bindings body.code
    let patterns := checkedClauses.map (fun (.clause pattern _ _) => pattern)
    checkExhaustive (← get).program (← get).inference state.module subjectType patterns
    let inner ← get
    let captures := inner.captures
    let receiver := if captures.any (fun c => c.mode == .owned) then .owned else if captures.any (fun c => c.mode == .unique) then .unique else .shared
    let body ← mapCorePlaces fuel (capturePlace captures) (.cases ⟨subject.id, []⟩ checkedClauses)
    let function : CoreFunction := ⟨identity, { signature with receiver := some receiver }, [subject], captures, receiver, body, none, span⟩
    let declaration : FunctionDecl := ⟨⟨identity, state.module, s!"pattern#{identity.localId}", .private, span⟩,
      { signature with receiver := some receiver }, [⟨subject.id, "_subject", some subjectType, false⟩], none, none, none⟩
    set { inner with locals := state.locals, captures := state.captures, closureDepth := state.closureDepth,
      unsafePermission := state.unsafePermission, permittedEffects := state.permittedEffects,
      effectContexts := state.effectContexts, functions := inner.functions ++ [function],
      program.functions := inner.program.functions ++ [declaration] }
    let type := Term.callable identity []
    ensureExpected type expected
    produce type span (fun dst => .closure dst identity [] captures false)

  def elaborateHandler (fuel : Nat) (span : Span) (body : Expr) (clauses : List HandlerClause)
      (expected : Option Term) : ElabM Elaborated := do
    let outer ← get
    let output ← match expected with | some type => pure type | none => infer (freshMeta .type)
    let computationType ← infer (freshMeta .type)
    let instances ← clauses.filterMap (fun clause => match clause with
      | .operation _ operation args .. => some (operation, args) | _ => none) |>.mapM fun (operation, args) => do
      let (effect, _) ← getRequired (outer.program.operation operation) .unknownName "handler names no operation"
      let _ ← bindArguments effect.generics args
      pure (.effect effect.header.id args)
    let permitted := match outer.permittedEffects with
      | .row known tails => Term.row (known ++ instances) tails
      | row => .row instances [row]
    modify fun s => { s with permittedEffects := permitted, effectContexts := instances :: s.effectContexts }
    let computation ← elaborate fuel body (some computationType)
    modify fun s => { s with permittedEffects := outer.permittedEffects, effectContexts := outer.effectContexts }
    let checked ← clauses.mapM fun clause => do
      let before := (← get).locals
      let (patterns, argumentTypes, continuation, policy, operationInfo, body) ← match clause with
        | .completion _ pattern body => pure ([pattern], [computation.type], none, none, none, body)
        | .operation clauseSpan operation effectInstance patterns continuation body => do
          let (effect, declaration) ← getRequired (outer.program.operation operation) .unknownName "unknown handled operation"
          let subs ← bindArguments effect.generics effectInstance
          let signature ← substituteSignature fuel subs declaration.signature
          let terminal := signature.output == .bottom
          require (!terminal || continuation.isNone) .invalidResumption "terminal operation has no continuation" clauseSpan
          let policy ← if terminal then pure none else do
            let (lower, upper) := declaration.quantity.getD (1, some 1)
            pure (some (← getRequired (ResumptionPolicy.parse lower upper) .invalidResumption "invalid resumption quantity" clauseSpan))
          if !terminal && continuation.isNone then
            require (policy.get!.tailResumeAllowed) .invalidResumption "once-only handler abbreviation cannot satisfy this resumption count" clauseSpan
          let continuation ← continuation.mapM fun parameter => do
            let type := Term.continuation parameter.id signature.output output outer.permittedEffects
            pure (⟨parameter.id, type, false, clauseSpan⟩ : TypedSlot)
          pure (patterns, signature.arguments, continuation, policy, some (operation, effectInstance), body)
      require (patterns.length == argumentTypes.length) .typeMismatch "handler payload pattern arity differs" span
      let patterns ← (patterns.zip argumentTypes).mapM fun (pattern, type) =>
        infer (checkPattern (← get).program outer.bindings outer.module none fuel type pattern)
      let bindings := (← patterns.mapM (fun pattern => patternBindings fuel pattern)).flatten
      let names := (← patterns.mapM (fun pattern => pattern.binders fuel)).flatten
      let locals := names.map fun (id, name, type) => (⟨id, name, type, false, outer.closureDepth⟩ : Local)
      let kLocals := continuation.toList.map fun slot => (⟨slot.id, "k", slot.type, false, outer.closureDepth⟩ : Local)
      modify fun s => { s with locals := kLocals ++ locals ++ before }
      let body ← elaborate fuel body (some output)
      modify fun s => { s with locals := before }
      match operationInfo with
      | none => return CoreHandler.completion (patterns.headD (.wildcard computation.type)) bindings body.code
      | some (operation, effectInstance) => return .operation operation effectInstance patterns bindings continuation policy body.code
    let completionPatterns := checked.filterMap (fun clause => match clause with | .completion pattern .. => some pattern | _ => none)
    if completionPatterns.isEmpty then infer (unifyTypes (← get).program computation.type output)
    else checkExhaustive (← get).program (← get).inference outer.module computation.type completionPatterns
    return ⟨output, .handle (← newId) computation.code checked⟩
end

def elaborateFunction (function : FunctionDecl) : ElabM Unit := do
  let state ← get
  let body ← getRequired function.body .missingEvidence "function body is unavailable"
  require (function.parameters.length == function.signature.arguments.length) .typeMismatch "declared parameter tuple arity differs"
  let locals := (function.parameters.zip function.signature.arguments).map fun (parameter, type) =>
    (⟨parameter.id, parameter.name, type, parameter.mutable, 0⟩ : Local)
  let identity ← newId
  let brand := Term.rigid identity .brand 1
  let region := Term.rigid identity .region 1
  let labelType := Term.label brand region function.signature.output
  let explicit := match function.signature.effects with | .row instances _ => instances | _ => []
  modify fun s => { s with module := function.header.module, locals := locals.reverse, captures := [], closureDepth := 0,
    unsafePermission := false, labelNames := [(function.header.name, labelType)],
    permittedEffects := function.signature.effects, effectContexts := [explicit],
    inference.assumptions := function.signature.constraints }
  let body ← match body with
    | .block _ statements result => elaborateBlock state.program.limits.elaboration statements result (some function.signature.output)
    | _ => elaborate state.program.limits.elaboration body (some function.signature.output)
  infer (solvePending (← get).program)
  let parameters := locals.map (fun local => (⟨local.id, local.type, local.mutable, function.header.span⟩ : TypedSlot))
  let core : CoreFunction := ⟨function.header.id, function.signature, parameters, [], .shared,
    .label identity brand region function.signature.output body.code, some brand, function.header.span⟩
  modify fun s => { s with functions := s.functions ++ [core], locals := [], captures := [], labelNames := [] }

def elaborateProgram (program : Program) (bindings : List Binding) : Check CoreProgram := do
  let first ← getRequired program.packages.head? .invalidSource "source closure has no package"
  let initial : Elaboration := { program, bindings, module := first.root,
    nextId := 1 + (program.functions.flatMap (fun f => f.parameters.map (·.id))).foldl max 0 }
  let action : ElabM Unit := do
    for function in program.functions do
      if function.body.isSome then elaborateFunction function
  let (_, state) ← action.run initial
  return ⟨state.program, state.functions, bindings, state.inference⟩

end Glorious.Semantics
