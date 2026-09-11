import Glorious.Semantics.Traits

namespace Glorious.Semantics

inductive PatternKey where
  | product (arity : Nat)
  | array (length : Nat)
  | constructor (declaration : DeclId)
  | reference (mode : Mutability)
  | scalar (value : ScalarValue)
  deriving BEq, DecidableEq, Repr

structure PatternConstructor where
  key : PatternKey
  fields : List Term
  deriving Repr

inductive CheckedPattern where
  | wildcard (type : Term)
  | binder (identity : Id) (name : String) (type : Term)
  | constructor (type : Term) (key : PatternKey) (fields : List CheckedPattern)
  deriving Repr

def CheckedPattern.type : CheckedPattern → Term
  | .wildcard type | .binder _ _ type | .constructor type .. => type

def CheckedPattern.binders : Nat → CheckedPattern → Check (List (Id × String × Term))
  | 0, _ => reject .resourceLimit "pattern binder traversal exhausted"
  | _, .wildcard _ => return []
  | _, .binder id name type => return [(id, name, type)]
  | fuel + 1, .constructor _ _ fields => return (← fields.mapM (CheckedPattern.binders fuel)).flatten

def constructorUniverse (program : Program) (inference : Inference) (from : ModuleId)
    (type : Term) : Check (Option (List PatternConstructor)) := do
  let type ← normalize program inference program.limits.normalization [] type
  match type with
  | .unit => return some [⟨.product 0, []⟩]
  | .bottom => return some []
  | .tuple fields => return some [⟨.product fields.length, fields⟩]
  | .array element (.constant (.integer _ _ length)) =>
    require (length ≥ 0 && length.toNat ≤ program.target.maxObjectSize) .invalidLayout "invalid array pattern length"
    return some [⟨.array length.toNat, List.replicate length.toNat element⟩]
  | .reference mode _ referent => return some [⟨.reference mode, [referent]⟩]
  | .nominal declaration arguments =>
    let data ← getRequired (program.dataType declaration) .unknownName "unknown pattern subject type"
    if data.nonExhaustive && from.packageId != declaration.packageId then return none
    let subs ← bindArguments data.generics arguments
    return some (← data.variants.mapM fun variant => do
      return ⟨.constructor variant.header.id,
        ← variant.fields.mapM (fun field => substitute program.limits.normalization subs field.type)⟩)
  | .scalar .character => return none
  | .scalar (.integer ..) => return none
  | .scalar (.floating ..) => return none
  | _ => return none

def scalarValueType : ScalarValue → Term
  | .integer signed width _ => .scalar (.integer signed width)
  | .floating width _ => .scalar (.floating width)
  | .character _ => .scalar .character

def constantPattern : Nat → Term → Term → Check Pattern
  | 0, _, _ => reject .resourceLimit "structural constant pattern expansion exhausted"
  | fuel + 1, expected, constant =>
    match constant with
    | .constant (.floating ..) => reject .invalidSource "floating values are not structural equality patterns"
    | .constant value => do
      require (scalarValueType value == expected) .typeMismatch "constant pattern has a different type"
      return .constant constant
    | .constantTuple fields =>
      match expected with
      | .unit => do require fields.isEmpty .typeMismatch "unit pattern has fields"; return .tuple []
      | .tuple types => do
        require (fields.length == types.length) .typeMismatch "constant tuple pattern arity differs"
        return .tuple (← (types.zip fields).mapM (fun (t, v) => constantPattern fuel t v))
      | _ => reject .typeMismatch "tuple constant has a non-tuple expected type"
    | .constantConstructor declaration _ fields =>
      return .constructor declaration (fields.zipIdx |>.map (fun (field, index) => (index, .constant field))) false
    | _ => reject .invalidSource "pattern is not a closed structural constant"

def checkPattern (program : Program) (bindings : List Binding) (from : ModuleId)
    (borrowMode : Option (Mutability × Term)) : Nat → Term → Pattern → InferM CheckedPattern
  | 0, _, _ => reject .resourceLimit "pattern checking exhausted"
  | fuel + 1, expected, pattern => do
    let expected ← zonk program expected
    -- Borrow ergonomics produces references to fields, never copied owners.
    match expected, pattern with
    | .reference mode region referent, .reference .. => pure ()
    | .reference mode region referent, .binder .. => pure ()
    | .reference mode region referent, .wildcard => pure ()
    | .reference mode region referent, _ =>
      let nested ← checkPattern program bindings from (some (mode, region)) fuel referent pattern
      return .constructor expected (.reference mode) [nested]
    | _, _ => pure ()
    match pattern with
    | .wildcard => return .wildcard expected
    | .binder identity name forced =>
      if !forced then
        match resolve program bindings from .value ⟨[name]⟩ with
        | .ok binding =>
          if (program.constants.any (fun c => c.header.id == binding.declaration)) then
            return ← checkPattern program bindings from borrowMode fuel expected (.named ⟨[name]⟩ [])
        | .error d => if d.problem == .ambiguous then throw d
      let type := match borrowMode with | none => expected | some (mode, region) => .reference mode region expected
      return .binder identity name type
    | .named path fields =>
      let binding ← resolve program bindings from .value path
      match program.constants.find? (fun c => c.header.id == binding.declaration) with
      | some constant =>
        require fields.isEmpty .invalidSource "constant pattern cannot have arguments"
        let subs ← instantiate program constant.generics []
        let type ← substitute fuel subs constant.type
        unify program fuel expected type
        let value ← substitute fuel subs constant.value >>= zonk program
        checkPattern program bindings from borrowMode fuel expected (← constantPattern fuel expected value)
      | none =>
        checkPattern program bindings from borrowMode fuel expected
          (.constructor binding.declaration (fields.zipIdx |>.map (fun (field, index) => (index, field))) false)
    | .record path fields rest =>
      let binding ← resolve program bindings from .value path
      let (_, constructor) ← getRequired (program.constructor binding.declaration) .typeMismatch "record pattern names no constructor"
      let numbered ← fields.mapM fun (name, pattern) => do
        let index ← getRequired (constructor.fields.findIdx? (fun f => f.header.name == name)) .unknownName "unknown record field"
        return (index, pattern)
      checkPattern program bindings from borrowMode fuel expected (.constructor binding.declaration numbered rest)
    | .constant value =>
      let value ← zonk program value
      match value with
      | .constant (.floating ..) => reject .invalidSource "floating constant patterns are not admitted"
      | .constant scalar =>
        unify program fuel expected (scalarValueType scalar)
        return .constructor expected (.scalar scalar) []
      | _ => checkPattern program bindings from borrowMode fuel expected (← constantPattern fuel expected value)
    | .tuple fields =>
      let types ← match expected with
        | .unit => pure []
        | .tuple types => pure types
        | .meta .. => do
          let types ← fields.mapM (fun _ => freshMeta .type)
          unify program fuel expected (.tuple types)
          pure types
        | _ => reject .typeMismatch "tuple pattern requires the exact tuple argument shape"
      require (types.length == fields.length) .typeMismatch "tuple pattern arity differs"
      let checked ← (types.zip fields).mapM (fun (type, field) => checkPattern program bindings from borrowMode fuel type field)
      return .constructor expected (.product fields.length) checked
    | .array before after rest =>
      match expected with
      | .array element (.constant (.integer _ _ length)) =>
        require (length ≥ 0) .invalidLayout "negative array length"
        let count := length.toNat
        require (before.length + after.length ≤ count) .typeMismatch "array pattern exceeds its subject"
        require (rest.isSome || before.length + after.length == count) .typeMismatch "array pattern is not the declared fixed length"
        let middle := count - before.length - after.length
        let patterns := before ++ List.replicate middle Pattern.wildcard ++ after
        let checked ← patterns.mapM (checkPattern program bindings from borrowMode fuel element)
        -- A bound remainder is lowered as the exact resident subarray/view by
        -- the pattern projection phase, with all omitted indices retained.
        let checked := match rest with
          | none => checked
          | some _ => checked
        return .constructor expected (.array count) checked
      | _ => reject .typeMismatch "array pattern requires a normalized fixed array"
    | .constructor declaration fields rest =>
      let (data, variant) ← getRequired (program.constructor declaration) .unknownName "unknown nominal constructor"
      let subs ← instantiate program data.generics []
      let arguments := data.generics.map (fun b => (lookup b.id subs).getD (.param b.id b.kind))
      unify program fuel expected (.nominal data.header.id arguments)
      require (unique (fields.map Prod.fst)) .duplicate "duplicate pattern field"
      require (fields.all (fun (index, _) => index < variant.fields.length)) .unknownName "pattern field index is out of bounds"
      require (rest || fields.length == variant.fields.length) .typeMismatch "pattern omits fields without a remainder"
      if borrowMode.isNone then
        require data.dropHook.isNone .illegalDiscard "safe ownership deconstruction of a custom-Drop owner is forbidden"
        require (!data.nonExhaustive || data.header.id.packageId == from.packageId)
          .privacy "external ownership deconstruction of a non-exhaustive enum is forbidden"
      let checked ← variant.fields.zipIdx |>.mapM fun (field, index) => do
        require (visible from field.header) .privacy "pattern deconstructs a private field"
        let type ← substitute fuel subs field.type
        let pattern := (lookup index fields).getD .wildcard
        checkPattern program bindings from borrowMode fuel type pattern
      return .constructor expected (.constructor declaration) checked
    | .reference mode pattern =>
      match expected with
      | .reference actual region referent =>
        require (actual == mode || (actual == .unique && mode == .shared)) .typeMismatch "reference pattern access is incompatible"
        let checked ← checkPattern program bindings from (some (mode, region)) fuel referent pattern
        return .constructor expected (.reference mode) [checked]
      | _ => reject .typeMismatch "reference pattern requires a reference"

def specializePattern (constructor : PatternConstructor) (pattern : CheckedPattern) : Option (List CheckedPattern) :=
  match pattern with
  | .wildcard _ | .binder .. => some (constructor.fields.map CheckedPattern.wildcard)
  | .constructor _ key fields => if key == constructor.key then some fields else none

def specializeMatrix (constructor : PatternConstructor) (matrix : List (List CheckedPattern)) : List (List CheckedPattern) :=
  matrix.filterMap fun row => match row with
    | [] => none
    | head :: rest => (specializePattern constructor head).map (· ++ rest)

def defaultMatrix (matrix : List (List CheckedPattern)) : List (List CheckedPattern) :=
  matrix.filterMap fun row => match row with
    | (.wildcard _ | .binder ..) :: rest => some rest
    | _ => none

/-- Standard constructor-matrix usefulness. Infinite scalar domains require a
    default row; no finite set of scalar constants is assumed exhaustive. -/
def useful (program : Program) (inference : Inference) (from : ModuleId) :
    Nat → List Term → List (List CheckedPattern) → List CheckedPattern → Check Bool
  | 0, _, _, _ => reject .resourceLimit "pattern exhaustiveness search exhausted"
  | _ + 1, [], matrix, [] => return matrix.isEmpty
  | fuel + 1, type :: types, matrix, pattern :: patterns =>
    match pattern with
    | .constructor _ key fields => do
      let constructor : PatternConstructor := ⟨key, fields.map CheckedPattern.type⟩
      useful program inference from fuel (constructor.fields ++ types)
        (specializeMatrix constructor matrix) (fields ++ patterns)
    | _ => do
      match ← constructorUniverse program inference from type with
      | none => useful program inference from fuel types (defaultMatrix matrix) patterns
      | some constructors =>
        let alternatives ← constructors.mapM fun constructor =>
          useful program inference from fuel (constructor.fields ++ types)
            (specializeMatrix constructor matrix)
            (constructor.fields.map CheckedPattern.wildcard ++ patterns)
        return alternatives.any id
  | _, _, _, _ => reject .malformedCore "pattern matrix arity differs from its argument tuple"

def checkExhaustive (program : Program) (inference : Inference) (from : ModuleId)
    (type : Term) (patterns : List CheckedPattern) : Check Unit := do
  let _ ← patterns.foldlM (init := ([] : List (List CheckedPattern))) fun previous pattern => do
    let binders ← pattern.binders program.limits.normalization
    require (unique (binders.map (fun (id, _, _) => id)) && unique (binders.map (fun (_, name, _) => name)))
      .duplicate "a pattern binds a name more than once"
    require (← useful program inference from program.limits.solving [type] previous [pattern])
      .invalidSource "unreachable pattern clause"
    return previous ++ [[pattern]]
  require (!(← useful program inference from program.limits.solving [type]
    (patterns.map (fun pattern => [pattern])) [.wildcard type])) .invalidSource "non-exhaustive pattern callable"

end Glorious.Semantics
