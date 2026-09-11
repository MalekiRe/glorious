import Glorious.Semantics.Specialize

namespace Glorious.Semantics

/-- The Core binder inventory is shared by hygienic fusion and receiving-Core
validation. Declarations and uses are kept distinct; a missing use is an error. -/
def coreSlots : Nat → Core → Check (List TypedSlot)
  | 0, _ => reject .resourceLimit "Core binder inventory exhausted"
  | fuel + 1, core => do
    match core with
    | .step operation next =>
      let own := match operation with
        | .declare slot => [slot]
        | .deconstruct _ _ bindings => bindings.map (·.slot)
        | _ => []
      return own ++ (← coreSlots fuel next)
    | .bind slot a b => return slot :: ((← coreSlots fuel a) ++ (← coreSlots fuel b))
    | .scopeBlock _ body | .label _ _ _ _ body => coreSlots fuel body
    | .cases _ clauses => return (← clauses.mapM fun (.clause _ bindings body) => do
        return bindings.map (·.slot) ++ (← coreSlots fuel body)).flatten
    | .handle _ body clauses => return (← coreSlots fuel body) ++ (← clauses.mapM fun clause => do
        match clause with
        | .completion _ bindings body => return bindings.map (·.slot) ++ (← coreSlots fuel body)
        | .operation _ _ _ bindings k _ body => return bindings.map (·.slot) ++ k.toList ++ (← coreSlots fuel body)).flatten
    | _ => return []

def coreBrands : Nat → Core → Check (List Id)
  | 0, _ => reject .resourceLimit "Core brand inventory exhausted"
  | fuel + 1, core => do
    match core with
    | .step _ next => coreBrands fuel next
    | .bind _ a b => return (← coreBrands fuel a) ++ (← coreBrands fuel b)
    | .scopeBlock identity body | .label identity _ _ _ body => return identity :: (← coreBrands fuel body)
    | .cases _ clauses => return (← clauses.mapM (fun (.clause _ _ body) => coreBrands fuel body)).flatten
    | .handle identity body clauses => return identity :: ((← coreBrands fuel body) ++ (← clauses.mapM fun clause =>
        match clause with | .completion _ _ body | .operation _ _ _ _ _ _ body => coreBrands fuel body).flatten)
    | _ => return []

def renamePlace (renames : List (Id × Id)) (place : Place) : Place :=
  {
    root := (lookup place.root renames).getD place.root,
    projections := place.projections.map fun projection => match projection with
      | .dynamicIndex identity => .dynamicIndex ((lookup identity renames).getD identity)
      | _ => projection }

def renameLocalTerm (fuel : Nat) (renames : List (Id × Id)) (term : Term) : Check Term := do
  match fuel with
  | 0 => reject .resourceLimit "Core brand alpha-renaming exhausted"
  | fuel + 1 =>
    match term with
    | .rigid identity kind level => return .rigid ((lookup identity renames).getD identity) kind level
    | .continuation identity a b effects =>
      return .continuation ((lookup identity renames).getD identity)
        (← renameLocalTerm fuel renames a) (← renameLocalTerm fuel renames b) (← renameLocalTerm fuel renames effects)
    | _ => term.mapChildrenM (renameLocalTerm fuel renames)

def renameCore (fuel : Nat) (renames : List (Id × Id)) (core : Core) : Check Core := do
  let core ← mapCoreTerms fuel (renameLocalTerm fuel renames) core
  let core ← mapCorePlaces fuel (renamePlace renames) core
  let id := fun identity => (lookup identity renames).getD identity
  let slot := fun (slot : TypedSlot) => { slot with id := id slot.id }
  let bindings := fun (bindings : List PatternBinding) => bindings.map (fun b => { b with slot := slot b.slot })
  let rec visit : Nat → Core → Check Core
    | 0, _ => reject .resourceLimit "Core storage alpha-renaming exhausted"
    | fuel + 1, core => do
      match core with
      | .step operation next =>
        let operation := match operation with
          | .declare s => .declare (slot s)
          | .constant dst value => .constant (id dst) value
          | .literalView dst binding bytes => .literalView (id dst) binding bytes
          | .read dst source move => .read (id dst) source move
          | .construct dst constructor fields => .construct (id dst) constructor fields
          | .closure dst function args captures materialized => .closure (id dst) function args captures materialized
          | .borrow dst mode region source => .borrow (id dst) mode region source
          | .invoke dst call => .invoke (id dst) { call with identity := id call.identity }
          | .perform dst op args payload signature => .perform (id dst) op args payload signature
          | .deconstruct source pattern bs => .deconstruct source pattern (bindings bs)
          | .test dst source pattern a b => .test (id dst) source pattern a b
          | .machine dst binding args signature permission => .machine (id dst) binding args signature permission
          | _ => operation
        return .step operation (← visit fuel next)
      | .bind s a b => return .bind (slot s) (← visit fuel a) (← visit fuel b)
      | .scopeBlock identity body => return .scopeBlock (id identity) (← visit fuel body)
      | .label identity brand region type body => return .label (id identity) brand region type (← visit fuel body)
      | .cases subject clauses => return .cases subject (← clauses.mapM fun (.clause p bs body) =>
          return .clause p (bindings bs) (← visit fuel body))
      | .handle identity body clauses => return .handle (id identity) (← visit fuel body) (← clauses.mapM fun clause => do
          match clause with
          | .completion p bs body => return .completion p (bindings bs) (← visit fuel body)
          | .operation op args ps bs k q body => return .operation op args ps (bindings bs) (k.map slot) q (← visit fuel body))
      | .tail call => return .tail { call with identity := id call.identity }
      | _ => return core
  visit fuel core

structure FusionState where
  program : CoreProgram
  nextId : Id
  deriving Repr

abbrev FusionM := StateT FusionState Check

def hasControlCarrier (fuel : Nat) (type : Term) : Bool :=
  type.any fuel (fun term => match term with | .label .. | .environment .. => true | _ => false)

def fusionCallee (program : CoreProgram) (slots : List TypedSlot) (call : CallSite) : Check (Option CoreFunction) := do
  let slot ← getRequired (slots.find? (fun slot => slot.id == call.callee.root)) .malformedCore "invocation has no typed callee storage"
  let rec project : Nat → Term → List Projection → Check Term
    | 0, _, _ => reject .resourceLimit "fusion callee type projection exhausted"
    | _, type, [] => return type
    | fuel + 1, type, projection :: rest => do
      let type ← match type, projection with
        | .reference _ _ type, .dereference => pure type
        | .tuple fields, .field index => getRequired fields[index]? .malformedCore "callee field is out of bounds"
        | .array type _, .index _ => pure type
        | _, _ => reject .missingEvidence "callee projection lacks a resolved structural view"
      project fuel type rest
  let type ← project program.source.limits.normalization slot.type call.callee.projections
  let type := match type with | .reference _ _ type => type | _ => type
  match type with
  | .callable declaration _ => return program.function declaration
  | _ => return none

mutual
  def fuseCore (fuel : Nat) (active : List DeclId) (slots : List TypedSlot) (core : Core) : FusionM Core := do
    match fuel with
    | 0 => reject .resourceLimit "structural control fusion exhausted"
    | fuel + 1 =>
      match core with
      | .step (.invoke destination call) next =>
        let program := (← get).program
        let selected ← fusionCallee program slots call
        let needs := hasControlCarrier program.source.limits.normalization (.tuple (call.signature.arguments ++
          (selected.toList.flatMap (fun function => function.captures.map (·.type)))))
        if !needs then return .step (.invoke destination call) (← fuseCore fuel active slots next)
        let function ← getRequired selected .missingEvidence "label-bearing invocation has no structural callable body" call.span
        let body ← fuseInvocation fuel active function call
        let result ← getRequired (slots.find? (fun slot => slot.id == destination)) .malformedCore "fusion result lacks its declared type"
        return .bind result body (← fuseCore fuel active slots next)
      | .step operation next => return .step operation (← fuseCore fuel active slots next)
      | .bind slot a b => return .bind slot (← fuseCore fuel active slots a) (← fuseCore fuel active slots b)
      | .scopeBlock scope body => return .scopeBlock scope (← fuseCore fuel active slots body)
      | .label identity brand region type body => return .label identity brand region type (← fuseCore fuel active slots body)
      | .cases subject clauses => return .cases subject (← clauses.mapM fun (.clause p bs body) =>
          return .clause p bs (← fuseCore fuel active slots body))
      | .handle identity body clauses => return .handle identity (← fuseCore fuel active slots body) (← clauses.mapM fun clause => do
          match clause with
          | .completion p bs body => return .completion p bs (← fuseCore fuel active slots body)
          | .operation op args ps bs k q body => return .operation op args ps bs k q (← fuseCore fuel active slots body))
      | .tail call =>
        let program := (← get).program
        let selected ← fusionCallee program slots call
        let needs := hasControlCarrier program.source.limits.normalization (.tuple call.signature.arguments)
        if !needs then return core
        let function ← getRequired selected .missingEvidence "tail label helper has no structural body" call.span
        fuseInvocation fuel active function call
      | _ => return core

  def fuseInvocation (fuel : Nat) (active : List DeclId) (function : CoreFunction) (call : CallSite) : FusionM Core := do
    require (!active.contains function.declaration) .missingEvidence "recursive label helper requires a checked finite control backedge" call.span
    require (function.parameters.length == call.inputs.length) .malformedCore "fusion invocation tuple arity differs"
    let state ← get
    let localSlots ← coreSlots fuel function.body
    let captured := function.captures.map fun capture =>
      (⟨capture.parameter, capture.type, capture.mode == .unique, call.span⟩ : TypedSlot)
    let slots := function.parameters ++ captured ++ localSlots
    let ids := ((slots.map (·.id)) ++ (← coreBrands fuel function.body)).eraseDups
    let renames := ids.zipIdx |>.map fun (identity, index) => (identity, state.nextId + index)
    set { state with nextId := state.nextId + ids.length + 1 }
    let renamed := fun (slot : TypedSlot) => { slot with id := (lookup slot.id renames).getD slot.id }
    let body ← renameCore fuel renames function.body
    let body ← fuseCore fuel (function.declaration :: active) (slots.map renamed) body
    let arguments := (function.parameters.zip call.inputs).flatMap fun (parameter, input) =>
      let parameter := renamed parameter
      [CoreOp.declare parameter, .read parameter.id input.value true]
    let captures := function.captures.zipIdx |>.map fun (capture, index) =>
      (⟨renamed ⟨capture.parameter, capture.type, capture.mode == .unique, call.span⟩,
        [.field index], none⟩ : PatternBinding)
    let pattern := CheckedPattern.constructor (.callable function.declaration [])
      (.product captures.length) (captures.map (fun capture => .wildcard capture.slot.type))
    return .scopeBlock (state.nextId + ids.length)
      (coreStepList (arguments ++ [.deconstruct call.callee pattern captures]) body)
end

def validateCoreBindings (program : CoreProgram) : Check Unit := do
  for function in program.functions do
    let slots := function.parameters ++ function.captures.map (fun capture =>
      (⟨capture.parameter, capture.type, capture.mode == .unique, function.span⟩ : TypedSlot)) ++
      (← coreSlots program.source.limits.elaboration function.body)
    for place in ← coreInputs program.source.limits.elaboration function.body do
      require (slots.any (fun slot => slot.id == place.root)) .malformedCore "Core reads an unbound storage identity" function.span
    for slot in slots do
      require (slot.type.kind == .type) .kindMismatch "Core storage binder is not a value type" slot.span

def fuseProgram (program : CoreProgram) : Check CoreProgram := do
  let inventories ← program.functions.mapM fun function => do
    return function.parameters.map (·.id) ++ function.captures.map (·.parameter) ++
      (← coreSlots program.source.limits.elaboration function.body).map (·.id) ++
      (← coreBrands program.source.limits.elaboration function.body)
  let initial : FusionState := ⟨program, 1 + inventories.flatten.foldl max 0⟩
  let action : FusionM (List CoreFunction) := program.functions.mapM fun function => do
    let slots := function.parameters ++ function.captures.map (fun c => ⟨c.parameter, c.type, c.mode == .unique, function.span⟩) ++
      (← coreSlots program.source.limits.elaboration function.body)
    return { function with body := ← fuseCore program.source.limits.elaboration [function.declaration] slots function.body }
  let (functions, _) ← action.run initial
  let program := { program with functions }
  validateCoreBindings program
  return program

end Glorious.Semantics
