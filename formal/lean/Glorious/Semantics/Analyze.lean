import Glorious.Semantics.Elaborate
import Glorious.Semantics.Memory

namespace Glorious.Semantics

inductive Frame where
  | bind (destination : TypedSlot) (next : Core)
  | scope (identity previous : Id) (entrySlots : List Id)
  | label (identity : Id) (brand region resultType : Term) (previousScope : Id) (entrySlots : List Id)
  | handler (identity : Id) (clauses : List CoreHandler) (previousScope : Id) (entrySlots : List Id)
  | call (function : DeclId) (previousFrame previousScope : Id) (entrySlots : List Id)
  | resume (returnStack : List Frame) (returnWorld : World) (capturedSlots : List Id)
  deriving Repr

structure ContinuationState where
  identity : Id
  policy : ResumptionPolicy
  remaining : Nat
  destination : TypedSlot
  next : Core
  frames : List Frame
  snapshot : World
  capturedSlots : List Id
  handler : Frame
  consumed : Bool := false
  deriving Repr

inductive ExecutionMode where
  | symbolic | concrete
  deriving BEq, DecidableEq, Repr

structure MachineState where
  world : World
  frames : List Frame := []
  continuations : List ContinuationState := []
  nextContinuation : Id := 0
  nextFrame : Id := 1
  mode : ExecutionMode := .symbolic
  deriving Repr

inductive Completion where
  | returned (value : Value)
  | transferred (brand : Term) (value : Value)
  | outwardOperation (operation : DeclId) (effectInstance : List Term) (payload : List Value)
  | cancelled
  | diverged
  | fatal (reason : Fatal)
  | unknown (reason : UnknownReason)
  deriving Repr

structure Execution where
  state : MachineState
  outcome : Completion
  deriving Repr

abbrev Executions := List Execution

def worldAction (action : WorldM α) (state : MachineState) : Check (α × MachineState) := do
  let (result, world) ← action.run state.world
  return (result, { state with world })

def opInputs : CoreOp → List Place
  | .read _ source _ | .discard source | .borrow _ _ _ source => [source]
  | .assign destination source | .initializeOwner destination source => [source, destination]
  | .construct _ _ fields => fields
  | .closure _ _ _ captures _ => captures.map (·.source)
  | .invoke _ call => call.callee :: call.inputs.map (·.value)
  | .perform _ _ _ payload _ => payload
  | .deconstruct source .. | .test _ source .. => [source]
  | .machine _ _ arguments .. => arguments
  | .seal values => values
  | _ => []

def coreInputs : Nat → Core → Check (List Place)
  | 0, _ => reject .resourceLimit "Core dependency projection exhausted"
  | _, .result value => return [value]
  | fuel + 1, .step operation next => return opInputs operation ++ (← coreInputs fuel next)
  | fuel + 1, .bind _ computation next => return (← coreInputs fuel computation) ++ (← coreInputs fuel next)
  | fuel + 1, .scopeBlock _ body | fuel + 1, .label _ _ _ _ body => coreInputs fuel body
  | fuel + 1, .cases subject clauses => return subject :: (← clauses.mapM (fun (.clause _ _ body) => coreInputs fuel body)).flatten
  | fuel + 1, .handle _ body clauses => return (← coreInputs fuel body) ++ (← clauses.mapM (fun clause =>
      match clause with | .completion _ _ body | .operation _ _ _ _ _ _ body => coreInputs fuel body)).flatten
  | _, .tail call => return call.callee :: call.inputs.map (·.value)
  | _, .leave _ payload => return [payload]
  | _, .fatal _ => return []

def frameInputs (fuel : Nat) (frames : List Frame) : Check (List Place) := do
  return (← frames.mapM fun frame => match frame with
    | .bind _ next => coreInputs fuel next
    | .handler _ clauses _ _ => do
      return (← clauses.mapM fun clause => match clause with
        | .completion _ _ body | .operation _ _ _ _ _ _ body => coreInputs fuel body).flatten
    | _ => pure []).flatten

/-- A single dependency projection drives NLL, continuation capture and escape
    checks. Closure bodies contribute on invocation, never on formation. -/
def endDeadLoans (program : CoreProgram) (core : Core) (state : MachineState) : Check MachineState := do
  let places ← coreInputs program.source.limits.analysis core
  let places := places ++ (← frameInputs program.source.limits.analysis state.frames)
  let roots := places.map (·.root) |>.eraseDups
  let values := state.world.slots.filter (fun slot => roots.contains slot.declaration.id) |>.filterMap (·.value)
  let tree := (← values.mapM (valueTree program.source.limits.normalization)).flatten
  let direct := tree.filterMap (fun value => match value.head with | .reference loan => some loan | _ => none)
  let suspended := state.continuations.filter (! ·.consumed) |>.flatMap (fun k => k.snapshot.loans.filter (·.live) |>.map (·.identity))
  let live := direct ++ suspended
  let loans := state.world.loans.reverse
  let (_, state) ← worldAction (do
    for loan in loans do
      if loan.live && !live.contains loan.identity then
        let world ← get
        if !(world.loans.any (fun l => l.live && l.parent == some loan.identity)) then endLoan loan.identity) state
  return state

def instantiateSymbolic (program : Program) (inference : Inference) (type : Term) : WorldM Value := do
  let world ← get
  createValue program inference type (.symbolic world.nextOwner)

def constantValue (program : Program) (inference : Inference) : Nat → Term → Term → WorldM Value
  | 0, _, _ => reject .resourceLimit "constant materialization exhausted"
  | fuel + 1, expected, constant => do
    match constant with
    | .constant scalar =>
      validateScalar program.target scalar
      require (scalarValueType scalar == expected) .typeMismatch "constant materialization type differs"
      createValue program inference expected (.scalar scalar)
    | .constantTuple fields =>
      let types := match expected with | .tuple fields => fields | .unit => [] | _ => []
      require (types.length == fields.length) .typeMismatch "constant tuple shape differs"
      let values ← (types.zip fields).mapM (fun (type, field) => constantValue program inference fuel type field)
      createValue program inference expected (if fields.isEmpty then .unit else .constructor none) (values.map some)
    | .constantConstructor declaration arguments fields =>
      let (data, variant) ← getRequired (program.constructor declaration) .unknownName "constant constructor is unknown"
      let subs ← bindArguments data.generics arguments
      let types ← variant.fields.mapM (fun f => substitute fuel subs f.type)
      require (types.length == fields.length) .typeMismatch "constant nominal shape differs"
      let values ← (types.zip fields).mapM (fun (type, field) => constantValue program inference fuel type field)
      createValue program inference expected (.constructor (some declaration)) (values.map some)
    | .label brand _ _ => createValue program inference expected (.label brand)
    | _ => reject .invalidSource "constant evaluator accepts only closed structural values"

def keyMatches (head : ValueHead) (key : PatternKey) : Option Bool :=
  match head, key with
  | .symbolic _, _ => none
  | .unit, .product 0 => some true
  | .constructor none, .product _ | .constructor none, .array _ => some true
  | .constructor (some declaration), .constructor expected => some (declaration == expected)
  | .reference _, .reference _ => some true
  | .scalar value, .scalar expected => some (value == expected)
  | _, _ => some false

def patternPossible : Nat → Value → CheckedPattern → Check Bool
  | 0, _, _ => reject .resourceLimit "structural pattern decision exhausted"
  | _, _, .wildcard _ | _, _, .binder .. => return true
  | fuel + 1, value, .constructor _ key fields => do
    match keyMatches value.head key with
    | some false => return false
    | none => return true
    | some true =>
      if value.fields.isEmpty && fields.isEmpty then return true
      if value.head matches .reference _ then return true
      require (value.fields.length == fields.length) .malformedCore "pattern and initialized resident shape differ"
      let results ← (value.fields.zip fields).mapM fun (field, pattern) => do
        let field ← getRequired field .uninitialized "pattern inspects a moved-out field"
        patternPossible fuel field pattern
      return results.all id

def refineValue (program : Program) (inference : Inference) (pattern : CheckedPattern)
    (value : Value) : WorldM Value := do
  match pattern with
  | .wildcard _ | .binder .. => return value
  | .constructor _type key fields =>
    match value.head with
    | .symbolic origin =>
      let head := match key with
        | .product _ | .array _ => ValueHead.constructor none
        | .constructor declaration => .constructor (some declaration)
        | .scalar scalar => .scalar scalar
        | .reference _ => .symbolic origin
      let residents ← fields.mapM (fun pattern => instantiateSymbolic program inference pattern.type)
      let value := value.withHead head |>.withFields (residents.map some)
      match key with
      | .constructor declaration => modify fun s => { s with guards := s.guards ++ [.constructor origin declaration true] }
      | .scalar scalar => modify fun s => { s with guards := s.guards ++ [.scalar origin scalar true] }
      | _ => pure ()
      return value
    | _ => return value

def bindPattern (program : CoreProgram) (subject : Place) (pattern : CheckedPattern)
    (bindings : List PatternBinding) : WorldM Unit := do
  let world ← get
  let located ← locate program.source world subject
  let value ← lookupAddress program.source world located.address >>= fun value => getRequired value .moved "matching an unavailable value"
  let refined ← refineValue program.source program.inference pattern value
  updateAddress program.source located.address (some refined)
  for binding in bindings do
    if !((← get).slots.any (fun s => s.declaration.id == binding.slot.id)) then declareSlot binding.slot
    let source := { subject with projections := subject.projections ++ binding.projections }
    let value ← match binding.borrowed with
      | none => takeValue program.source source true
      | some (mode, region) => borrowValue program.source program.inference source mode region
    initializeValue program.source ⟨binding.slot.id, []⟩ value
  -- Authorized structural deconstruction discharges the shell, never a Drop
  -- hook. Remaining resident fields still pass the ordinary cleanup compiler.
  match pattern with
  | .wildcard _ => discardValue program.source subject
  | .binder .. => pure ()
  | .constructor _ (.reference _) _ =>
    if (← lookupAddress program.source (← get) located.address).isSome then discardValue program.source subject
  | .constructor .. =>
    if let some remainder ← lookupAddress program.source (← get) located.address then
      require remainder.dropHook.isNone .illegalDiscard "cannot deconstruct a custom-Drop owner"
      updateAddress program.source located.address (some (remainder.withFields remainder.fields true))
      discardValue program.source subject

def simpleOperation (program : CoreProgram) (operation : CoreOp) : WorldM Unit := do
  let source := program.source
  match operation with
  | .declare slot => declareSlot slot
  | .constant destination constant =>
    let slot ← getSlot (← get) destination
    let value ← constantValue source program.inference source.limits.normalization slot.declaration.type constant
    initializeValue source ⟨destination, []⟩ value
  | .literalView destination binding bytes =>
    let admitted ← getRequired (source.imports.find? (fun i => i.identity == binding && i.kind == .staticData)) .missingImport "static literal binding is not admitted"
    let value ← createValue source program.inference admitted.signature.output (.staticView binding.localId bytes.length)
    initializeValue source ⟨destination, []⟩ value
  | .read destination place forced =>
    let value ← takeValue source place forced
    initializeValue source ⟨destination, []⟩ value
  | .initializeOwner destination place =>
    let value ← takeValue source place true
    initializeValue source destination value
  | .assign destination place =>
    let value ← takeValue source place true
    assignValue source destination value
  | .construct destination declaration fields =>
    let values ← fields.mapM (fun field => takeValue source field true)
    let slot ← getSlot (← get) destination
    let value ← createValue source program.inference slot.declaration.type (.constructor declaration) (values.map some)
    initializeValue source ⟨destination, []⟩ value
  | .closure destination function arguments captures materialized =>
    let values ← captures.mapM fun capture => match capture.mode with
      | .owned => takeValue source capture.source false
      | .shared => borrowValue source program.inference capture.source .shared
          (.rigid capture.parameter .region 0)
      | .unique => borrowValue source program.inference capture.source .unique
          (.rigid capture.parameter .region 0)
    let slot ← getSlot (← get) destination
    let head := if (source.operation function).isSome then ValueHead.operation function arguments
      else .callable function arguments materialized
    let world ← get
    let capability := Principal.residents (values.map Value.capability)
    let value := Value.owned world.nextOwner slot.declaration.type capability none false head (values.map some)
    set { world with nextOwner := world.nextOwner + 1 }
    initializeValue source ⟨destination, []⟩ value
  | .borrow destination mode region place =>
    let value ← borrowValue source program.inference place mode region
    initializeValue source ⟨destination, []⟩ value
  | .endLoan identity => endLoan identity
  | .discard place => discardValue source place
  | .deconstruct subject pattern bindings => bindPattern program subject pattern bindings
  | .seal places =>
    let values ← places.mapM fun place => do
      let world ← get
      let located ← locate source world place
      lookupAddress source world located.address >>= fun value => getRequired value .uninitialized "escape boundary sees an unavailable value"
    sealValues source values
  | .test destination place pattern positive negative =>
    let world ← get
    let located ← locate source world place
    let value ← lookupAddress source world located.address >>= fun value => getRequired value .uninitialized "test subject is unavailable"
    checkAccess source world located .read
    let possible ← patternPossible source.limits.analysis value pattern
    let brand := if possible then positive else negative
    let slot ← getSlot (← get) destination
    let value ← createValue source program.inference slot.declaration.type (.bindingPack brand)
    initializeValue source ⟨destination, []⟩ value
  | .machine destination binding arguments signature permission =>
    let admitted ← getRequired (source.imports.find? (fun i => i.identity == binding)) .missingImport "machine leaf has no admitted identity"
    require (!signature.unsafeCall || permission) .unsafeOperation "machine operation requires unsafe permission"
    require (admitted.signature.arguments == signature.arguments && admitted.signature.output == signature.output)
      .incompatibleABI "machine operation differs from its admitted signature"
    let values ← arguments.mapM (fun place => takeValue source place true)
    let value ← executeLeaf source program.inference admitted values >>= fun value =>
      getRequired value .malformedCore "terminal leaf must be dispatched as a control outcome"
    initializeValue source ⟨destination, []⟩ value
  | .invoke .. | .perform .. => reject .malformedCore "control operation was not dispatched through the invocation machine"

def slotsSince (world : World) (entry : List Id) : List Id :=
  world.slots.filter (fun s => !entry.contains s.declaration.id) |>.map (fun s => s.declaration.id)

def cleanupFrame (program : CoreProgram) (frame : Frame) (payload : List Value)
    (boundary : CleanupBoundary) (state : MachineState) : Check MachineState := do
  let (entry, priorScope, priorFrame) := match frame with
    | .scope _ prior entry | .label _ _ _ _ prior entry | .handler _ _ prior entry =>
      (entry, some prior, none)
    | .call _ prior scope entry => (entry, some scope, some prior)
    | _ => (state.world.slots.map (fun (s : Slot) => s.declaration.id), none, none)
  let ending := slotsSince state.world entry
  let (_, state) ← worldAction (cleanupSlots program.source ending payload boundary) state
  return { state with
    world.scope := priorScope.getD state.world.scope,
    world.frame := priorFrame.getD state.world.frame }

def snapshotReplayable (program : CoreProgram) (snapshot : World) (slots : List Id) : Check Unit := do
  let residents := snapshot.slots.filter (fun s => slots.contains s.declaration.id) |>.filterMap (·.value)
  let values := (← residents.mapM (valueTree program.source.limits.normalization)).flatten
  require (values.all (fun value => value.capability == .duplicable)) .replay "multi-shot capture includes a nonduplicable initialized resident"
  require (!(snapshot.loans.any (fun loan => loan.live && loan.mode == .unique))) .replay "multi-shot capture includes a live unique loan"
  require (!(values.any (fun value => match value.head with | .label _ => true | _ => false))) .replay "multi-shot capture includes a label destination"
  require (!(snapshot.loans.any (fun loan => loan.live && loan.hole))) .loanHole "continuation capture includes an initialization hole"

def resumptionCapture (program : CoreProgram) (policy : ResumptionPolicy)
    (snapshot : World) (slots : List Id) : Check Unit := do
  require (!(snapshot.loans.any (fun loan => loan.live && loan.hole))) .loanHole "continuation capture crosses an unrestored unique-reference hole"
  match policy with
  | .optional =>
    let _ ← (cleanupSlots program.source slots [] .cancellation).run snapshot
    pure ()
  | .exact count _ _ => if count > 1 then snapshotReplayable program snapshot slots else pure ()

def checkTail (program : CoreProgram) (state : MachineState) (call : CallSite)
    (payload : List Value) : Check Unit := do
  require (call.signature.abi == .glorious) .tail "cross-ABI tail transfer has no declared mandatory-tail convention"
  let afterCallWork := state.frames.takeWhile (fun frame => match frame with | .call .. => false | _ => true)
  for frame in afterCallWork do
    match frame with
    | .bind .. => reject .tail "reachable work remains after the tail invocation" call.span
    | .handler .. => reject .tail "tail invocation retains an unfused dynamic handler" call.span
    | .resume .. => reject .tail "tail invocation retains a resumption return continuation" call.span
    | _ => pure ()
  let values := (← payload.mapM (valueTree program.source.limits.normalization)).flatten
  for value in values do
    match value.head with
    | .reference identity =>
      let loan ← getRequired (state.world.loans.find? (fun l => l.identity == identity && l.live)) .escapingReference "tail payload has an ended reference"
      let slot ← getSlot state.world loan.origin.slot
      require (slot.frame != state.world.frame) .tail "tail payload references reclaimed current-frame storage" call.span
    | .label brand =>
      let label ← getRequired (state.world.labels.find? (fun l => l.brand == brand)) .escapingBrand "inactive label in tail payload"
      require (label.frame != state.world.frame) .tail "tail payload retains a current-frame label destination" call.span
    | _ => pure ()

mutual
  def execute (program : CoreProgram) : Nat → Core → MachineState → Check Executions
    | 0, _, state => return [⟨state, .unknown .resourceLimit⟩]
    | fuel + 1, core, initial => do
      let state ← endDeadLoans program core initial
      match core with
      | .result place =>
        let (value, state) ← worldAction (takeValue program.source place true) state
        finish program fuel value state
      | .step (.invoke destination call) next => invoke program fuel destination next call state false
      | .step (.perform destination operation effectInstance payload signature) next =>
        let (values, state) ← worldAction (payload.mapM (fun p => takeValue program.source p true)) state
        performOperation program fuel destination next operation effectInstance signature values state
      | .step operation next =>
        let (_, state) ← worldAction (simpleOperation program operation) state
        execute program fuel next state
      | .bind destination computation next =>
        execute program fuel computation { state with frames := .bind destination next :: state.frames }
      | .scopeBlock identity body =>
        let frame := Frame.scope identity state.world.scope (state.world.slots.map (fun s => s.declaration.id))
        execute program fuel body { state with world.scope := identity, frames := frame :: state.frames }
      | .label identity brand region resultType body =>
        require (!(state.world.labels.any (fun l => l.brand == brand))) .escapingBrand "label brand is already active"
        let label : LabelState := ⟨brand, region, resultType, state.world.frame, identity⟩
        let frame := Frame.label identity brand region resultType state.world.scope (state.world.slots.map (fun s => s.declaration.id))
        execute program fuel body { state with
          world.scope := identity,
          world.labels := label :: state.world.labels, frames := frame :: state.frames }
      | .handle identity body clauses =>
        let frame := Frame.handler identity clauses state.world.scope (state.world.slots.map (fun s => s.declaration.id))
        execute program fuel body { state with world.scope := identity, frames := frame :: state.frames }
      | .cases subject clauses => selectCases program fuel subject clauses state
      | .tail call => invoke program fuel 0 (.fatal .runtimeFault) call state true
      | .leave brand place =>
        let (value, state) ← worldAction (takeValue program.source place true) state
        transferLabel program fuel brand value state
      | .fatal reason => return [⟨state, .fatal reason⟩]
  termination_by fuel _ _ => fuel

  def finish (program : CoreProgram) (fuel : Nat) (value : Value) (state : MachineState) : Check Executions := do
    match fuel with
    | 0 => return [⟨state, .unknown .resourceLimit⟩]
    | fuel + 1 =>
      match state.frames with
      | [] => return [⟨state, .returned value⟩]
      | frame :: rest =>
        let state := { state with frames := rest }
        match frame with
        | .bind destination next =>
          let (_, state) ← worldAction (do
            declareSlot destination
            initializeValue program.source ⟨destination.id, []⟩ value) state
          execute program fuel next state
        | .scope .. => finish program fuel value (← cleanupFrame program frame [value] .normalReturn state)
        | .label _ brand _ resultType _ _ =>
          require (value.type == resultType || value.type == .bottom) .typeMismatch "label result type differs"
          let state ← cleanupFrame program frame [value] .normalReturn state
          finish program fuel value { state with world.labels := state.world.labels.filter (fun label => label.brand != brand) }
        | .handler _ clauses _ _ =>
          let state ← cleanupFrame program frame [value] .normalReturn state
          let completions := clauses.filterMap fun clause => match clause with
            | .completion pattern bindings body => some (CoreCase.clause pattern bindings body)
            | _ => none
          if completions.isEmpty then finish program fuel value state else
            let destination : TypedSlot := ⟨state.world.nextOwner + 1000000000, value.type, false, {}⟩
            let (_, state) ← worldAction (do declareSlot destination; initializeValue program.source ⟨destination.id, []⟩ value) state
            selectCases program fuel ⟨destination.id, []⟩ completions state
        | .call .. => finish program fuel value (← cleanupFrame program frame [value] .normalReturn state)
        | .resume returnStack returnWorld captured =>
          let ending := state.world.slots.filter (fun s => captured.contains s.declaration.id) |>.map (fun s => s.declaration.id)
          let (_, state) ← worldAction (cleanupSlots program.source ending [value] .normalReturn) state
          let world := { returnWorld with
            nextOwner := max returnWorld.nextOwner state.world.nextOwner,
            nextLoan := max returnWorld.nextLoan state.world.nextLoan,
            cleanup := state.world.cleanup, effects := state.world.effects }
          finish program fuel value { state with world, frames := returnStack }
  termination_by fuel

  def selectCases (program : CoreProgram) (fuel : Nat) (subject : Place)
      (clauses : List CoreCase) (state : MachineState) : Check Executions := do
    match fuel, clauses with
    | 0, _ => return [⟨state, .unknown .resourceLimit⟩]
    | _, [] => reject .malformedCore "checked exhaustive pattern matrix has no matching clause"
    | fuel + 1, .clause pattern bindings body :: rest =>
      let located ← locate program.source state.world subject
      let value ← lookupAddress program.source state.world located.address >>= fun v => getRequired v .moved "matching an unavailable subject"
      let possible ← patternPossible program.source.limits.analysis value pattern
      if !possible then selectCases program fuel subject rest state else
        let (_, matched) ← worldAction (bindPattern program subject pattern bindings) state
        let yes ← execute program fuel body matched
        let unknown := match value.head, pattern with
          | .symbolic _, .constructor .. => true
          | _, _ => false
        if !unknown || rest.isEmpty then return yes
        let guard := match value.head, pattern with
          | .symbolic origin, .constructor _ (.constructor declaration) _ => some (Guard.constructor origin declaration false)
          | .symbolic origin, .constructor _ (.scalar scalar) _ => some (Guard.scalar origin scalar false)
          | _, _ => none
        let noState := { state with world.guards := state.world.guards ++ guard.toList }
        if consistentGuards noState.world.guards then
          return yes ++ (← selectCases program fuel subject rest noState)
        else return yes
  termination_by fuel

  def transferLabel (program : CoreProgram) (fuel : Nat) (brand : Term)
      (value : Value) (state : MachineState) : Check Executions := do
    match fuel, state.frames with
    | 0, _ => return [⟨state, .unknown .resourceLimit⟩]
    | _, [] => return [⟨state, .transferred brand value⟩]
    | fuel + 1, frame :: rest =>
      let state := { state with frames := rest }
      match frame with
      | .call .. => reject .tail "label helper was not fused into its active destination frame"
      | .label _ target _ type _ _ =>
        let state ← cleanupFrame program frame [value] (.labelTransfer ⟨⟨0, 0⟩, 0⟩) state
        let state := { state with world.labels := state.world.labels.filter (fun label => label.brand != target) }
        if target == brand then
          require (value.type == type) .typeMismatch "nonlocal payload type differs from label result"
          finish program fuel value state
        else transferLabel program fuel brand value state
      | _ => transferLabel program fuel brand value (← cleanupFrame program frame [value] (.labelTransfer ⟨⟨0, 0⟩, 0⟩) state)
  termination_by fuel
  decreasing_by all_goals simp [wfParam]

  def invoke (program : CoreProgram) (fuel : Nat) (destination : Id) (next : Core)
      (call : CallSite) (state : MachineState) (tail : Bool) : Check Executions := do
    match fuel with
    | 0 => return [⟨state, .unknown .resourceLimit⟩]
    | fuel + 1 =>
      let (callee, state) ← worldAction (takeValue program.source call.callee true) state
      let (arguments, state) ← worldAction (call.inputs.mapM (fun input => takeValue program.source input.value true)) state
      require (arguments.length == call.signature.arguments.length) .malformedCore "invocation input tuple differs from its signature"
      if tail then checkTail program state call (callee :: arguments)
      match callee.head with
      | .label brand =>
        let payload ← getRequired arguments.head? .typeMismatch "label invocation requires one payload"
        transferLabel program fuel brand payload state
      | .continuation identity =>
        let payload ← getRequired arguments.head? .typeMismatch "resumption invocation requires one payload"
        resumeContinuation program fuel destination next identity payload state tail
      | .operation operation effectInstance =>
        performOperation program fuel destination next operation effectInstance call.signature arguments state
      | .callable declaration genericArguments _ =>
        if let some (data, variant) := program.source.constructor declaration then
          let (value, state) ← worldAction (createValue program.source program.inference
            (.nominal data.header.id genericArguments) (.constructor (some variant.header.id)) (arguments.map some)) state
          deliverCall program fuel destination next value state tail
        else if let some function := program.function declaration then
          let entry := state.world.slots.map (fun s => s.declaration.id)
          let previousFrame := state.world.frame
          let previousScope := state.world.scope
          let frames := if tail then state.frames else
            .call declaration previousFrame previousScope entry :: .bind ⟨destination, call.signature.output, false, call.span⟩ next :: state.frames
          let frame := if tail then previousFrame else state.nextFrame
          let state := { state with
            world.frame := frame, world.scope := frame,
            frames, nextFrame := state.nextFrame + (if tail then 0 else 1) }
          let (_, state) ← worldAction (do
            require (function.parameters.length == arguments.length || function.parameters.length == 1)
              .typeMismatch "specialized callable argument packing differs"
            let arguments ← if function.parameters.length == arguments.length then pure arguments else do
              let parameter ← getRequired function.parameters.head? .malformedCore "missing packed argument parameter"
              pure [← createValue program.source program.inference parameter.type (.constructor none) (arguments.map some)]
            for (parameter, argument) in function.parameters.zip arguments do
              declareSlot parameter
              initializeValue program.source ⟨parameter.id, []⟩ argument
            require (function.captures.length == callee.fields.length) .malformedCore "callable capture tuple differs from frozen environment"
            for (capture, field) in function.captures.zip callee.fields do
              let value ← getRequired field .uninitialized "invocation reads a moved capture"
              let slot : TypedSlot := ⟨capture.parameter, value.type, capture.mode == .unique, call.span⟩
              declareSlot slot
              initializeValue program.source ⟨slot.id, []⟩ value) state
          execute program fuel function.body state
        else
          let declaration ← getRequired (program.source.function declaration) .missingEvidence "callable body and runtime binding are unavailable"
          let binding ← getRequired declaration.runtimeBinding .missingEvidence "opaque callable cannot supply missing control evidence"
          require (!(callee.type.any program.source.limits.normalization (fun t => match t with | .label .. | .environment .. => true | _ => false)))
            .escapingBrand "proof-only environment or label would cross an opaque boundary"
          let output ← getRequired (program.source.imports.find? (fun i => i.identity == binding)) .missingImport "unadmitted runtime call"
          let (value, state) ← worldAction (instantiateSymbolic program.source program.inference output.signature.output) state
          deliverCall program fuel destination next value state tail
      | .reference _ => reject .missingEvidence "borrowed callable requires its selected receiver/capture binding relation"
      | .symbolic _ => return [⟨state, .unknown .opaqueInvocation⟩]
      | _ => reject .typeMismatch "value has no callable identity"
  termination_by fuel

  def deliverCall (program : CoreProgram) (fuel destination : Nat) (next : Core)
      (value : Value) (state : MachineState) (tail : Bool) : Check Executions := do
    match fuel with
    | 0 => return [⟨state, .unknown .resourceLimit⟩]
    | fuel + 1 =>
      if tail then finish program fuel value state else
        let (_, state) ← worldAction (initializeValue program.source ⟨destination, []⟩ value) state
        execute program fuel next state
  termination_by fuel

  def performOperation (program : CoreProgram) (fuel destination : Nat) (next : Core)
      (operation : DeclId) (effectInstance : List Term) (signature : Signature)
      (payload : List Value) (state : MachineState) : Check Executions := do
    match fuel with
    | 0 => return [⟨state, .unknown .resourceLimit⟩]
    | fuel + 1 =>
      let (effect, _declaration) ← getRequired (program.source.operation operation) .unknownName "performed operation has no declaration"
      let exact := Term.effect effect.header.id effectInstance
      let state := { state with world.effects := state.world.effects ++ [exact] }
      let rec search : Nat → List Frame → List Frame → Check Executions
        | 0, _, _ => return [⟨state, .unknown .resourceLimit⟩]
        | _, _, [] => return [⟨state, .outwardOperation operation effectInstance payload⟩]
        | remaining + 1, inner, frame :: outer =>
          match frame with
          | .handler _identity clauses priorScope entry => do
            let candidates := clauses.filterMap fun clause => match clause with
              | .operation candidate arguments patterns bindings continuation policy body =>
                if candidate == operation && arguments == effectInstance then some (patterns, bindings, continuation, policy, body) else none
              | _ => none
            let rec select : Nat → List (List CheckedPattern × List PatternBinding × Option TypedSlot × Option ResumptionPolicy × Core) → Check Executions
              | 0, _ => return [⟨state, .unknown .resourceLimit⟩]
              | count + 1, [] => search count (inner ++ [frame]) outer
              | count + 1, (patterns, _bindings, continuation, policy, body) :: rest => do
                require (patterns.length == payload.length) .typeMismatch "operation payload arity differs from handler"
                let accepted ← (payload.zip patterns).mapM (fun (value, pattern) => patternPossible program.source.limits.analysis value pattern)
                if !(accepted.all id) then select count rest else
                  let captured := slotsSince state.world entry
                  let clauseState := { state with frames := outer, world.scope := priorScope }
                  let (clauseState, continuationValue) ← if signature.output == .bottom then do
                      let (_, clauseState) ← worldAction (cleanupSlots program.source captured payload (.terminalEffect operation)) clauseState
                      pure (clauseState, none)
                    else do
                      let policy ← getRequired policy .invalidResumption "resumptive handler lacks a checked quantity"
                      resumptionCapture program policy state.world captured
                      let id := state.nextContinuation
                      let target : TypedSlot := ⟨destination, signature.output, false, {}⟩
                      let saved : ContinuationState := ⟨id, policy, policy.maximum, target, next, inner,
                        state.world, captured, frame, false⟩
                      let clauseState := { clauseState with
                        nextContinuation := id + 1,
                        continuations := clauseState.continuations ++ [saved],
                        world.slots := clauseState.world.slots.filter (fun s => !captured.contains s.declaration.id) }
                      let type := match continuation with
                        | some slot => slot.type
                        | none => .continuation id signature.output signature.output signature.effects
                      let (value, clauseState) ← worldAction (createValue program.source program.inference type (.continuation id)) clauseState
                      pure (clauseState, some value)
                  let (_, clauseState) ← worldAction (do
                    for (value, pattern) in payload.zip patterns do
                      let slot : TypedSlot := ⟨value.identity + 2000000000, value.type, false, {}⟩
                      declareSlot slot
                      initializeValue program.source ⟨slot.id, []⟩ value
                      let ownBindings ← patternBindings program.source.limits.analysis pattern
                      bindPattern program ⟨slot.id, []⟩ pattern ownBindings
                    if let some slot := continuation then
                      declareSlot slot
                      initializeValue program.source ⟨slot.id, []⟩ (← getRequired continuationValue .invalidResumption "missing continuation authority")) clauseState
                  let results ← execute program count body clauseState
                  if continuation.isNone && continuationValue.isSome then
                    let continuationValue ← getRequired continuationValue .invalidResumption "missing implicit resumption authority"
                    let .continuation id := continuationValue.head
                      | reject .invalidResumption "implicit resumption value has no continuation identity"
                    return (← results.mapM fun result => match result.outcome with
                      | .returned value => resumeContinuation program count destination next id value result.state true
                      | _ => pure [result]).flatten
                  else return results
            termination_by count _ => count
            select remaining candidates
          | _ => search remaining (inner ++ [frame]) outer
      termination_by remaining _ _ => remaining
      search fuel [] state.frames
  termination_by fuel

  def resumeContinuation (program : CoreProgram) (fuel destination : Nat) (next : Core)
      (identity : Id) (value : Value) (state : MachineState) (tail : Bool) : Check Executions := do
    match fuel with
    | 0 => return [⟨state, .unknown .resourceLimit⟩]
    | fuel + 1 =>
      let authority ← getRequired (state.continuations.find? (fun k => k.identity == identity && !k.consumed))
        .invalidResumption "resumption authority was already consumed or is unknown"
      require (authority.remaining > 0) .invalidResumption "resumption invoked too many times through its aliases"
      require (value.type == authority.destination.type) .typeMismatch "resumption payload has the wrong type"
      let final := authority.remaining == 1
      if !final then snapshotReplayable program authority.snapshot authority.capturedSlots
      let saved := { authority with remaining := authority.remaining - 1, consumed := final }
      let continuations := state.continuations.map (fun k => if k.identity == identity then saved else k)
      let captured := authority.snapshot.slots.filter (fun s => authority.capturedSlots.contains s.declaration.id)
      let (captured, copyWorld) ← if final then pure (captured, state.world) else do
        let action : WorldM (List Slot) := captured.mapM fun slot => do
          return { slot with value := ← slot.value.mapM (cloneValue program.source.limits.normalization) }
        action.run state.world
      let world := {
        authority.snapshot with
        slots := copyWorld.slots ++ captured,
        nextOwner := max copyWorld.nextOwner authority.snapshot.nextOwner,
        nextLoan := max copyWorld.nextLoan authority.snapshot.nextLoan,
        cleanup := copyWorld.cleanup, effects := copyWorld.effects }
      let returnStack := if tail then state.frames else .bind ⟨destination, value.type, false, {}⟩ next :: state.frames
      let frames := authority.frames ++ [authority.handler,
        .resume returnStack state.world authority.capturedSlots]
      let resumed := { state with world, continuations, frames }
      let (_, resumed) ← worldAction (do
        if !((← get).slots.any (fun s => s.declaration.id == authority.destination.id)) then declareSlot authority.destination
        initializeValue program.source ⟨authority.destination.id, []⟩ value) resumed
      execute program fuel authority.next resumed
  termination_by fuel
end

structure FunctionFacts where
  declaration : DeclId
  outcomes : Executions
  inputOwners : List (InputPosition × Id)
  effects : List Term
  referenceReturns : List (List Nat × InputPosition × List Projection)
  deriving Repr

def collectReferenceReturns (program : CoreProgram) (parameters : List TypedSlot)
    (result : Value) (world : World) : Check (List (List Nat × InputPosition × List Projection)) := do
  let rec visit : Nat → List Nat → Value → Check (List (List Nat × InputPosition × List Projection))
    | 0, _, _ => reject .resourceLimit "reference-return provenance projection exhausted"
    | fuel + 1, path, value => do
      let own ← match value.head with
        | .reference identity => do
          let loan ← getRequired (world.loans.find? (fun l => l.identity == identity && l.live)) .escapingReference "returned reference has no live provenance"
          let parameter ← getRequired (parameters.findIdx? (fun parameter => parameter.id == loan.origin.slot)) .escapingReference "returned reference originates in a local owner"
          pure [(path, InputPosition.argument parameter, loan.origin.fields.map Projection.field)]
        | _ => pure []
      let nested ← value.fields.zipIdx |>.mapM fun (field, index) => match field with
        | none => pure [] | some field => visit fuel (path ++ [index]) field
      return own ++ nested.flatten
  visit program.source.limits.analysis [] result

def analyzeFunction (program : CoreProgram) (function : CoreFunction) : Check FunctionFacts := do
  let initial : World := { frame := 1, scope := 1 }
  let initializeOwner : WorldM (List (InputPosition × Id)) := do
    let ordinary ← function.parameters.zipIdx |>.mapM fun (parameter, index) => do
      declareSlot parameter
      let value ← instantiateSymbolic program.source program.inference parameter.type
      initializeValue program.source ⟨parameter.id, []⟩ value
      pure (InputPosition.argument index, value.identity)
    let captured ← function.captures.zipIdx |>.mapM fun (capture, index) => do
      let slot : TypedSlot := ⟨capture.parameter, capture.type, capture.mode == .unique, function.span⟩
      declareSlot slot
      let value ← instantiateSymbolic program.source program.inference capture.type
      initializeValue program.source ⟨slot.id, []⟩ value
      pure (InputPosition.capture [index], value.identity)
    return ordinary ++ captured
  let (inputs, world) ← initializeOwner.run initial
  let outcomes ← execute program program.source.limits.analysis function.body ⟨world, [], [], 0, 2, .symbolic⟩
  require (outcomes.length ≤ program.source.limits.alternatives) .resourceLimit "guarded execution alternatives exceed the declared limit"
  let referenceReturns ← outcomes.mapM fun execution => do
    match execution.outcome with
    | .unknown reason =>
      reject (if reason == .resourceLimit then .resourceLimit else .missingEvidence)
        "semantic control obligation remains unknown; it is not an empty outcome set" function.span
    | .returned value =>
      require (value.type == function.signature.output || value.type == .bottom) .typeMismatch "function result differs from its declared type"
      let (_, _) ← (sealValues program.source [value]).run execution.state.world
      let references ← collectReferenceReturns program function.parameters value execution.state.world
      let ending := execution.state.world.slots.map (fun s => s.declaration.id)
      let _ ← (cleanupSlots program.source ending [value] .normalReturn).run execution.state.world
      return references
    | .transferred .. => reject .escapingBrand "unresolved direct label transfer escapes the compiled function"
    | .outwardOperation operation effectInstance _ =>
      let (effect, _) ← getRequired (program.source.operation operation) .unknownName "unknown outward operation"
      let _ ← (solveRowInclusion program.source function.signature.effects (.row [.effect effect.header.id effectInstance] [])).run program.inference
      return []
    | .cancelled =>
      let ending := execution.state.world.slots.map (fun s => s.declaration.id)
      let _ ← (cleanupSlots program.source ending [] .cancellation).run execution.state.world
      return []
    | .fatal _ | .diverged => return []
  let effects := outcomes.flatMap (fun result => result.state.world.effects) |>.eraseDups
  return ⟨function.declaration, outcomes, inputs, effects, referenceReturns.flatten⟩

structure AnalyzedProgram where
  core : CoreProgram
  functions : List FunctionFacts
  deriving Repr

def analyzeProgram (program : CoreProgram) : Check AnalyzedProgram := do
  let functions ← program.functions.mapM (analyzeFunction program)
  return ⟨program, functions⟩

end Glorious.Semantics
