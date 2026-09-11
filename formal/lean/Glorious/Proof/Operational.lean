import Glorious.Semantics.Analyze
import Glorious.Proof.Resources

/-! Unbounded operational rules for the compiler's semantic Core. The bounded
analyzer is an implementation to be proved against these rules, not their
definition. Captures and parameters enter through the same invocation ledger.
The rules distinguish source faults from an implementation getting stuck. -/
namespace Glorious.Semantics.Spec

inductive Observation where
  | effect (operation : DeclId) (arguments : List Term) (payload : List Value)
  | cleanup (event : CleanupEvent)
  | host (binding : DeclId) (arguments : List Value) (result : Option Value)
  | tail (declaration : DeclId)
  deriving Repr

inductive Result where
  | returned (value : Value)
  | transfer (brand : Term) (value : Value)
  | operation (identity : DeclId) (arguments : List Term) (payload : List Value)
  | cancelled
  | fatal (reason : Fatal)
  deriving Repr

mutual
inductive Matches : Value → CheckedPattern → Prop where
  | wildcard {value} : Matches value (.wildcard value.type)
  | binder {value identity name} : Matches value (.binder identity name value.type)
  | product {value patterns}
      (head : value.head = .constructor none ∨ value.head = .unit)
      (fields : MatchesFields value.fields patterns) :
      Matches value (.constructor value.type (.product patterns.length) patterns)
  | array {value patterns}
      (head : value.head = .constructor none)
      (fields : MatchesFields value.fields patterns) :
      Matches value (.constructor value.type (.array patterns.length) patterns)
  | constructor {value declaration patterns}
      (head : value.head = .constructor (some declaration))
      (fields : MatchesFields value.fields patterns) :
      Matches value (.constructor value.type (.constructor declaration) patterns)
  | scalar {value scalar} (head : value.head = .scalar scalar) :
      Matches value (.constructor value.type (.scalar scalar) [])

inductive MatchesFields : List (Option Value) → List CheckedPattern → Prop where
  | nil : MatchesFields [] []
  | cons {value values pattern patterns} (head : Matches value pattern)
      (tail : MatchesFields values patterns) : MatchesFields (some value :: values) (pattern :: patterns)
end

def FirstCase (value : Value) (clauses : List CoreCase) (selected : CoreCase) : Prop :=
  ∃ before after pattern bindings body,
    clauses = before ++ selected :: after ∧ selected = .clause pattern bindings body ∧
    Matches value pattern ∧ ∀ prior ∈ before,
      ∀ pattern bindings body, prior = .clause pattern bindings body → ¬ Matches value pattern

def FirstOperation (operation : DeclId) (arguments : List Term) (payload : List Value)
    (clauses : List CoreHandler) (selected : CoreHandler) : Prop :=
  ∃ before after patterns bindings continuation policy body,
    clauses = before ++ selected :: after ∧
    selected = .operation operation arguments patterns bindings continuation policy body ∧
    Glorious.Proof.Forall₂ Matches payload patterns ∧
    ∀ prior ∈ before, ∀ patterns bindings continuation policy body,
      prior = .operation operation arguments patterns bindings continuation policy body →
      ¬ Glorious.Proof.Forall₂ Matches payload patterns

structure Dispatch (operation : DeclId) (arguments : List Term) (payload : List Value)
    (stack : List Frame) where
  inner : List Frame
  identity : Id
  clauses : List CoreHandler
  scope : Id
  entry : List Id
  outer : List Frame
  clause : CoreHandler
  reconstruct : stack = inner ++ .handler identity clauses scope entry :: outer
  first : FirstOperation operation arguments payload clauses clause
  skipped : ∀ frame ∈ inner, ∀ identity clauses scope entry,
    frame = .handler identity clauses scope entry →
    ¬ ∃ selected, FirstOperation operation arguments payload clauses selected

inductive Declares : World → TypedSlot → World → Prop where
  | fresh {before slot}
      (fresh : ∀ existing ∈ before.slots, existing.declaration.id ≠ slot.id) :
      Declares before slot { before with
        nextAllocation := before.nextAllocation + 1,
        slots := before.slots ++ [⟨slot, before.frame, before.scope, ⟨before.nextAllocation, []⟩, none⟩] }

inductive FreshValue (program : Program) : World → Term → ValueHead → List (Option Value) → Value → World → Prop where
  | create {before type head fields principal hook}
      (permission : PrincipalOf program type principal)
      (hookIdentity : hook = (match type with
        | .nominal declaration _ => (program.dataType declaration).bind (·.dropHook)
        | _ => none)) :
      FreshValue program before type head fields
        (.owned before.nextOwner type principal hook false head fields)
        { before with nextOwner := before.nextOwner + 1 }

inductive TakesAll (program : Program) : World → List Place → List Value → World → Prop where
  | nil {world} : TakesAll program world [] [] world
  | cons {before middle after place places value values}
      (head : Takes program before place value middle)
      (tail : TakesAll program middle places values after) :
      TakesAll program before (place :: places) (value :: values) after

inductive FormsCaptures (program : Program) : World → List Capture → List Value → World → Prop where
  | nil {world} : FormsCaptures program world [] [] world
  | owned {before middle after capture captures value values}
      (mode : capture.mode = .owned)
      (read : Reads program before capture.source false value middle)
      (rest : FormsCaptures program middle captures values after) :
      FormsCaptures program before (capture :: captures) (value :: values) after
  | borrowed {before middle after capture captures value values mode region}
      (modeCorrect : (capture.mode = .shared ∧ mode = .shared) ∨ (capture.mode = .unique ∧ mode = .unique))
      (read : Borrows program before capture.source mode region value middle)
      (rest : FormsCaptures program middle captures values after) :
      FormsCaptures program before (capture :: captures) (value :: values) after

inductive BindsInputs (program : Program) :
    World → List (InputPosition × TypedSlot × Value) → World → Prop where
  | nil {world} : BindsInputs program world [] world
  | cons {before declared middle after position slot value rest}
      (declaration : Declares before slot declared)
      (initialization : Initializes program declared ⟨slot.id, []⟩ value middle)
      (remaining : BindsInputs program middle rest after) :
      BindsInputs program before ((position, slot, value) :: rest) after

def AllInputs (function : CoreFunction) (arguments captures : List Value) :
    List (InputPosition × TypedSlot × Value) :=
  ((function.parameters.zip arguments).zipIdx.map fun ((slot, value), index) => (.argument index, slot, value)) ++
  ((function.captures.zip captures).zipIdx.map fun ((capture, value), index) =>
    (.capture [index], ⟨capture.parameter, value.type, capture.mode == .unique, function.span⟩, value))

structure InvocationBinding (program : CoreProgram) (function : CoreFunction)
    (callee : Value) (arguments : List Value) (before after : World) : Prop where
  selected : function ∈ program.functions
  calleeIdentity : ∃ generic materialized, callee.head = .callable function.declaration generic materialized
  arity : function.parameters.length = arguments.length
  types : Glorious.Proof.Forall₂ (fun value type => value.type = type) arguments function.signature.arguments
  captureValues : ∃ captures,
    callee.fields = captures.map some ∧ captures.length = function.captures.length ∧
    BindsInputs program.source before (AllInputs function arguments captures) after
  receiverRestoration : function.receiver ≠ .owned →
    ∀ resident path, ResidentAt callee path resident →
      resident.capability = .duplicable ∨ ∃ address, Stored after address resident

inductive PatternTransition (program : CoreProgram) :
    World → Place → CheckedPattern → List PatternBinding → World → Prop where
  | binder {before declared after subject value identity name type located}
      (location : Denotes program.source before subject located)
      (stored : Stored before located.address value) (typed : value.type = type)
      (declaration : Declares before ⟨identity, type, false, {}⟩ declared)
      (moved : ∃ middle, Takes program.source declared subject value middle ∧
        Initializes program.source middle ⟨identity, []⟩ value after) :
      PatternTransition program before subject (.binder identity name type)
        [⟨⟨identity, type, false, {}⟩, [], none⟩] after
  | wildcard {before after subject located value}
      (location : Denotes program.source before subject located) (stored : Stored before located.address value)
      (destroyed : Disposes program.source before subject after) :
      PatternTransition program before subject (.wildcard value.type) [] after
  | structural {before after subject pattern bindings located value}
      (location : Denotes program.source before subject located) (stored : Stored before located.address value)
      (selected : Matches value pattern)
      (noHook : value.dropHook = none)
      (bindingsTransferred : ∀ binding ∈ bindings, ∃ resident,
        Stored after ⟨binding.slot.id, []⟩ resident ∧ resident.type = binding.slot.type)
      (linearTransfer : ∀ path resident, ResidentAt value path resident → resident.capability = .exact →
        ∃ destination, Stored after destination resident)
      (shellConsumed : ¬ Stored after located.address value)
      (noDuplicate : WorldWellFormed after) :
      PatternTransition program before subject pattern bindings after

inductive Atom (program : CoreProgram) : World → CoreOp → World → Prop where
  | declare {before after slot} : Declares before slot after → Atom program before (.declare slot) after
  | constant {before middle after destination slot scalar value}
      (declared : slot ∈ before.slots) (identity : slot.declaration.id = destination)
      (valid : ValidScalar program.source.target scalar)
      (type : slot.declaration.type = scalarValueType scalar)
      (created : FreshValue program.source before slot.declaration.type (.scalar scalar) [] value middle)
      (stored : Initializes program.source middle ⟨destination, []⟩ value after) :
      Atom program before (.constant destination (.constant scalar)) after
  | unit {before middle after destination value}
      (created : FreshValue program.source before .unit .unit [] value middle)
      (stored : Initializes program.source middle ⟨destination, []⟩ value after) :
      Atom program before (.constant destination (.constantTuple [])) after
  | read {before middle after destination source forced value}
      (read : Reads program.source before source forced value middle)
      (write : Initializes program.source middle ⟨destination, []⟩ value after) :
      Atom program before (.read destination source forced) after
  | initializeOwner {before middle after destination source value}
      (read : Takes program.source before source value middle)
      (write : Initializes program.source middle destination value after) :
      Atom program before (.initializeOwner destination source) after
  | assignment {before moved vacant after destination source value located slot}
      (read : Takes program.source before source value moved)
      (location : Denotes program.source moved destination located)
      (owner : slot ∈ moved.slots) (identity : slot.declaration.id = located.address.slot)
      (mutable : slot.declaration.mutable = true ∨ located.throughLoan.isSome = true)
      (dispose : (¬ ∃ old, Stored moved located.address old) ∧ vacant = moved ∨
        Disposes program.source moved destination vacant)
      (write : Initializes program.source vacant destination value after) :
      Atom program before (.assign destination source) after
  | borrow {before middle after destination source mode region value}
      (borrow : Borrows program.source before source mode region value middle)
      (write : Initializes program.source middle ⟨destination, []⟩ value after) :
      Atom program before (.borrow destination mode region source) after
  | endLoan {before after identity} : EndsLoan before identity after → Atom program before (.endLoan identity) after
  | discard {before after source} : Disposes program.source before source after → Atom program before (.discard source) after
  | deconstruct {before after subject pattern bindings} :
      PatternTransition program before subject pattern bindings after →
      Atom program before (.deconstruct subject pattern bindings) after
  | construct {before taken created after destination constructor places values slot value}
      (read : TakesAll program.source before places values taken)
      (declared : slot ∈ taken.slots) (identity : slot.declaration.id = destination)
      (shape : FieldTypes program.source slot.declaration.type (.constructor constructor) (values.map Value.type))
      (create : FreshValue program.source taken slot.declaration.type (.constructor constructor) (values.map some) value created)
      (write : Initializes program.source created ⟨destination, []⟩ value after) :
      Atom program before (.construct destination constructor places) after
  | closure {before captured created after destination declaration arguments captures materialized values value slot function}
      (present : function ∈ program.functions) (identity : function.declaration = declaration)
      (shape : function.captures = captures)
      (formation : FormsCaptures program.source before captures values captured)
      (slotPresent : slot ∈ captured.slots) (slotIdentity : slot.declaration.id = destination)
      (type : slot.declaration.type = .callable declaration arguments)
      (fresh : FreshValue program.source captured slot.declaration.type (.callable declaration arguments materialized)
        (values.map some) value created)
      (write : Initializes program.source created ⟨destination, []⟩ value after) :
      Atom program before (.closure destination declaration arguments captures materialized) after
  | seal {world places}
      (valuesValid : ∀ place ∈ places, ∃ located value,
        Denotes program.source world place located ∧ Stored world located.address value ∧ HandleValid world value)
      (closed : ∀ available ∈ world.availability, available.pending = false) :
      Atom program world (.seal places) world

inductive Control where
  | run (code : Core)
  | returning (value : Value)
  | transfer (brand : Term) (value : Value)
  | request (operation : DeclId) (arguments : List Term) (signature : Signature)
      (payload : List Value) (destination : Id) (next : Core)
  | done (result : Result)

structure Configuration where
  control : Control
  machine : MachineState

def FrameEntry : Frame → Option (List Id × Id × Option Id)
  | .scope _ prior entry | .label _ _ _ _ prior entry | .handler _ _ prior entry => some (entry, prior, none)
  | .call _ frame scope entry => some (entry, scope, some frame)
  | _ => none

def FrameDisposition (before after : MachineState) (frame : Frame) (payload : List Value)
    (boundary : CleanupBoundary) : Prop :=
  ∃ entry scope caller, FrameEntry frame = some (entry, scope, caller) ∧
    ExitDisposition before.world after.world
      (before.world.slots.filterMap fun slot => if slot.declaration.id ∈ entry then none else some slot.declaration.id)
      payload boundary ∧ after.world.scope = scope ∧
    after.world.frame = caller.getD before.world.frame ∧ after.frames = before.frames

def CapturedSlots (world : World) (entry : List Id) : List Id :=
  world.slots.filterMap fun slot => if slot.declaration.id ∈ entry then none else some slot.declaration.id

structure Capturable (world : World) (slots : List Id) (policy : ResumptionPolicy) : Prop where
  restored : ∀ loan ∈ world.loans, loan.live = true → loan.origin.slot ∈ slots → loan.hole = false
  cancellation : policy.required = 0 → ∃ after, ExitDisposition world after slots [] .cancellation
  replay : 1 < policy.maximum → ∀ slot ∈ world.slots, slot.declaration.id ∈ slots →
    ∀ root, slot.value = some root → ∀ path value, ResidentAt root path value → value.capability = .duplicable
  labels : 1 < policy.maximum → ∀ label ∈ world.labels,
    ¬ ∃ slot ∈ world.slots, slot.declaration.id ∈ slots ∧ slot.scope = label.scope

inductive BindsPatterns (program : CoreProgram) :
    World → List Value → List CheckedPattern → World → Prop where
  | nil {world} : BindsPatterns program world [] [] world
  | cons {before declared initialized matched after value values pattern patterns slot bindings}
      (type : slot.type = value.type)
      (declaration : Declares before slot declared)
      (write : Initializes program.source declared ⟨slot.id, []⟩ value initialized)
      (bind : PatternTransition program initialized ⟨slot.id, []⟩ pattern bindings matched)
      (rest : BindsPatterns program matched values patterns after) :
      BindsPatterns program before (value :: values) (pattern :: patterns) after

inductive ClonesSlots : List Slot → Id → List Slot → Id → Prop where
  | nil {next} : ClonesSlots [] next [] next
  | vacant {slot slots next result stop} (vacant : slot.value = none)
      (rest : ClonesSlots slots next result stop) : ClonesSlots (slot :: slots) next (slot :: result) stop
  | live {slot slots value next copy middle result stop}
      (live : slot.value = some value) (clone : Copies value next copy middle)
      (rest : ClonesSlots slots middle result stop) :
      ClonesSlots (slot :: slots) next ({ slot with value := some copy } :: result) stop

structure Resumes (program : CoreProgram) (identity : Id) (payload : Value)
    (returnStack : List Frame) (before after : MachineState) (next : Core) where
  authority : ContinuationState
  present : authority ∈ before.continuations
  same : authority.identity = identity
  live : authority.consumed = false
  remaining : 0 < authority.remaining
  typed : payload.type = authority.destination.type
  restored : ∀ loan ∈ authority.snapshot.loans, loan.live = true → loan.hole = false
  captured : List Slot
  owners : Id
  snapshot : (authority.remaining = 1 ∧ captured = authority.snapshot.slots.filter
      (fun slot => authority.capturedSlots.contains slot.declaration.id) ∧ owners = before.world.nextOwner) ∨
    (1 < authority.remaining ∧ ClonesSlots (authority.snapshot.slots.filter
      (fun slot => authority.capturedSlots.contains slot.declaration.id)) before.world.nextOwner captured owners)
  uniqueSlots : ((before.world.slots ++ captured).map (·.declaration.id)).Nodup
  binding : ∃ world, world = { authority.snapshot with
      slots := before.world.slots ++ captured,
      nextOwner := owners, cleanup := before.world.cleanup, effects := before.world.effects } ∧
    Initializes program.source world ⟨authority.destination.id, []⟩ payload after.world
  code : next = authority.next
  stack : after.frames = authority.frames ++ [authority.handler,
    .resume returnStack before.world authority.capturedSlots]
  ledger : after.continuations = before.continuations.map fun item =>
    if item.identity == identity then { item with
      remaining := item.remaining - 1,
      consumed := item.remaining == 1 } else item

def TailFrame : Frame → Prop
  | .bind .. | .scope .. | .call .. => True
  | _ => False

structure TailDisposition (before after : MachineState) (payload : List Value) where
  removed : List Frame
  retained : List Frame
  split : before.frames = removed ++ retained
  lawfulFrames : ∀ frame ∈ removed, TailFrame frame
  nearestCaller : ∀ frame ∈ retained, (∃ declaration caller scope entry,
    frame = .call declaration caller scope entry) → frame ∉ removed
  cleanup : ExitDisposition before.world after.world
    (before.world.slots.filterMap fun slot => if slot.frame = before.world.frame then some slot.declaration.id else none)
    payload .properTail
  continuation : after.frames = retained
  noGrowth : after.frames.length ≤ before.frames.length

inductive Step (program : CoreProgram) : Configuration → Option Observation → Configuration → Prop where
  | atom {code next before after}
      (transition : Atom program before.world code after.world)
      (control : after.frames = before.frames)
      (continuations : after.continuations = before.continuations) :
      Step program ⟨.run (.step code next), before⟩ none ⟨.run next, after⟩
  | result {place before world value}
      (read : Takes program.source before.world place value world) :
      Step program ⟨.run (.result place), before⟩ none ⟨.returning value, { before with world }⟩
  | bind {slot computation next state} :
      Step program ⟨.run (.bind slot computation next), state⟩ none
        ⟨.run computation, { state with frames := .bind slot next :: state.frames }⟩
  | bound {slot next state rest value declared world}
      (stack : state.frames = .bind slot next :: rest)
      (declaration : Declares state.world slot declared)
      (stored : Initializes program.source declared ⟨slot.id, []⟩ value world) :
      Step program ⟨.returning value, state⟩ none ⟨.run next, { state with world, frames := rest }⟩
  | returned {state value} (empty : state.frames = []) :
      Step program ⟨.returning value, state⟩ none ⟨.done (.returned value), state⟩
  | scope {identity code state} :
      Step program ⟨.run (.scopeBlock identity code), state⟩ none
        ⟨.run code, { state with
          world.scope := identity,
          frames := .scope identity state.world.scope (state.world.slots.map (·.declaration.id)) :: state.frames }⟩
  | finishScope {value before after identity prior entry rest}
      (stack : before.frames = .scope identity prior entry :: rest)
      (cleanup : FrameDisposition { before with frames := rest } after (.scope identity prior entry) [value] .normalReturn) :
      Step program ⟨.returning value, before⟩ none ⟨.returning value, after⟩
  | finishCall {value before after declaration caller scope entry rest}
      (stack : before.frames = .call declaration caller scope entry :: rest)
      (cleanup : FrameDisposition { before with frames := rest } after (.call declaration caller scope entry) [value] .normalReturn) :
      Step program ⟨.returning value, before⟩ none ⟨.returning value, after⟩
  | finishLabel {value before after identity brand region type prior entry rest}
      (stack : before.frames = .label identity brand region type prior entry :: rest)
      (typeCorrect : Subtype program.source [] value.type type)
      (cleanup : FrameDisposition { before with frames := rest } after (.label identity brand region type prior entry) [value] .normalReturn) :
      Step program ⟨.returning value, before⟩ none
        ⟨.returning value, { after with world.labels := after.world.labels.filter (fun label => label.brand != brand) }⟩
  | rejoin {value before after identity brand region type prior entry rest}
      (stack : before.frames = .label identity brand region type prior entry :: rest)
      (typeCorrect : Subtype program.source [] value.type type)
      (cleanup : FrameDisposition { before with frames := rest } after (.label identity brand region type prior entry)
        [value] (.labelTransfer ⟨⟨0, identity⟩, identity⟩)) :
      Step program ⟨.transfer brand value, before⟩ none
        ⟨.returning value, { after with world.labels := after.world.labels.filter (fun label => label.brand != brand) }⟩
  | unwind {value brand before after frame rest}
      (stack : before.frames = frame :: rest)
      (notTarget : ∀ identity region type prior entry, frame ≠ .label identity brand region type prior entry)
      (cleanup : FrameDisposition { before with frames := rest } after frame [value] (.labelTransfer ⟨⟨0, 0⟩, 0⟩)) :
      Step program ⟨.transfer brand value, before⟩ none ⟨.transfer brand value, after⟩
  | unwindBind {value brand state slot next rest} (stack : state.frames = .bind slot next :: rest) :
      Step program ⟨.transfer brand value, state⟩ none ⟨.transfer brand value, { state with frames := rest }⟩
  | label {identity brand region type body state}
      (fresh : ∀ active ∈ state.world.labels, active.brand ≠ brand) :
      Step program ⟨.run (.label identity brand region type body), state⟩ none
        ⟨.run body, { state with
          world.scope := identity,
          world.labels := ⟨brand, region, type, state.world.frame, identity⟩ :: state.world.labels,
          frames := .label identity brand region type state.world.scope (state.world.slots.map (·.declaration.id)) :: state.frames }⟩
  | leave {brand place state world value}
      (read : Takes program.source state.world place value world) :
      Step program ⟨.run (.leave brand place), state⟩ none ⟨.transfer brand value, { state with world }⟩
  | handle {identity body clauses state} :
      Step program ⟨.run (.handle identity body clauses), state⟩ none
        ⟨.run body, { state with
          world.scope := identity,
          frames := .handler identity clauses state.world.scope (state.world.slots.map (·.declaration.id)) :: state.frames }⟩
  | cases {subject clauses pattern bindings body before world located value}
      (location : Denotes program.source before.world subject located)
      (stored : Stored before.world located.address value)
      (selected : FirstCase value clauses (.clause pattern bindings body))
      (bound : PatternTransition program before.world subject pattern bindings world) :
      Step program ⟨.run (.cases subject clauses), before⟩ none ⟨.run body, { before with world }⟩
  | perform {destination operation arguments payload signature next before world values}
      (read : TakesAll program.source before.world payload values world) :
      Step program ⟨.run (.step (.perform destination operation arguments payload signature) next), before⟩
        (some (.effect operation arguments values))
        ⟨.request operation arguments signature values destination next, { before with world }⟩
  | invoke {destination next call before argumentsWorld receiverWorld world callee arguments function}
      (receiver : Takes program.source before.world call.callee callee receiverWorld)
      (argumentsRead : TakesAll program.source receiverWorld (call.inputs.map (·.value)) arguments argumentsWorld)
      (binding : InvocationBinding program function callee arguments
        { argumentsWorld with frame := before.nextFrame, scope := before.nextFrame } world) :
      Step program ⟨.run (.step (.invoke destination call) next), before⟩ none
        ⟨.run function.body, { before with
          world, nextFrame := before.nextFrame + 1,
          frames := .call function.declaration before.world.frame before.world.scope
            (before.world.slots.map (·.declaration.id)) ::
            .bind ⟨destination, call.signature.output, false, call.span⟩ next :: before.frames }⟩
  | tailInvoke {call before receiverWorld argumentsWorld disposed world callee arguments function}
      (receiver : Takes program.source before.world call.callee callee receiverWorld)
      (argumentsRead : TakesAll program.source receiverWorld (call.inputs.map (·.value)) arguments argumentsWorld)
      (disposition : TailDisposition { before with world := argumentsWorld } disposed (callee :: arguments))
      (binding : InvocationBinding program function callee arguments disposed.world world) :
      Step program ⟨.run (.tail call), before⟩ (some (.tail function.declaration))
        ⟨.run function.body, { disposed with world }⟩
  | invokeLabel {destination next call before receiverWorld world callee value brand}
      (receiver : Takes program.source before.world call.callee callee receiverWorld)
      (identity : callee.head = .label brand)
      (argument : TakesAll program.source receiverWorld (call.inputs.map (·.value)) [value] world) :
      Step program ⟨.run (.step (.invoke destination call) next), before⟩ none
        ⟨.transfer brand value, { before with world }⟩
  | resume {destination next call before receiverWorld argumentsWorld callee identity value after resumed}
      (receiver : Takes program.source before.world call.callee callee receiverWorld)
      (selected : callee.head = .continuation identity)
      (argument : TakesAll program.source receiverWorld (call.inputs.map (·.value)) [value] argumentsWorld)
      (transition : Resumes program identity value
        (.bind ⟨destination, call.signature.output, false, call.span⟩ next :: before.frames)
        { before with world := argumentsWorld } after resumed) :
      Step program ⟨.run (.step (.invoke destination call) next), before⟩ none ⟨.run resumed, after⟩
  | terminalOperation {destination next operation arguments signature payload before patterns bindings body bound}
      {after : MachineState}
      (dispatch : Dispatch operation arguments payload before.frames)
      (clause : dispatch.clause = .operation operation arguments patterns bindings none none body)
      (terminal : signature.output = .bottom)
      (cleanup : ExitDisposition before.world after.world (CapturedSlots before.world dispatch.entry)
        payload (.terminalEffect operation))
      (bind : BindsPatterns program after.world payload patterns bound) :
      Step program ⟨.request operation arguments signature payload destination next, before⟩ none
        ⟨.run body, { after with world := bound, frames := dispatch.outer }⟩
  | suspendedOperation {destination next operation arguments signature payload before patterns bindings slot policy body
      saved removed created bound continuationValue}
      (dispatch : Dispatch operation arguments payload before.frames)
      (clause : dispatch.clause = .operation operation arguments patterns bindings (some slot) (some policy) body)
      (resumptive : signature.output ≠ .bottom)
      (capture : Capturable before.world (CapturedSlots before.world dispatch.entry) policy)
      (snapshot : saved = (⟨before.nextContinuation, policy, policy.maximum,
        ⟨destination, signature.output, false, {}⟩, next, dispatch.inner, before.world,
        CapturedSlots before.world dispatch.entry,
        .handler dispatch.identity dispatch.clauses dispatch.scope dispatch.entry, false⟩ : ContinuationState))
      (remove : removed = { before.world with
        slots := before.world.slots.filter
          (fun item => !saved.capturedSlots.contains item.declaration.id), scope := dispatch.scope })
      (fresh : FreshValue program.source removed slot.type (.continuation saved.identity) [] continuationValue created)
      (binding : ∃ declared middle, Declares created slot declared ∧
        Initializes program.source declared ⟨slot.id, []⟩ continuationValue middle ∧
        BindsPatterns program middle payload patterns bound) :
      Step program ⟨.request operation arguments signature payload destination next, before⟩ none
        ⟨.run body, { before with
          world := bound, frames := dispatch.outer,
          continuations := before.continuations ++ [saved], nextContinuation := before.nextContinuation + 1 }⟩
  | outward {destination next operation arguments signature payload state}
      (unhandled : ¬ Nonempty (Dispatch operation arguments payload state.frames)) :
      Step program ⟨.request operation arguments signature payload destination next, state⟩ none
        ⟨.done (.operation operation arguments payload), state⟩
  | fatal {reason state} :
      Step program ⟨.run (.fatal reason), state⟩ none ⟨.done (.fatal reason), state⟩

def Initial (program : CoreProgram) (entry : DeclId) (configuration : Configuration) : Prop :=
  ∃ function ∈ program.functions,
    function.declaration = entry ∧ function.parameters = [] ∧ function.captures = [] ∧
    configuration.control = .run function.body ∧
    configuration.machine.world = { frame := 1, scope := 1 } ∧
    configuration.machine.frames = [] ∧ configuration.machine.continuations = [] ∧
    configuration.machine.nextFrame = 2 ∧ configuration.machine.nextContinuation = 0 ∧
    configuration.machine.mode = .concrete

def CoreSystem (program : CoreProgram) (entry : DeclId) : Glorious.Proof.TransitionSystem Observation Result where
  State := Configuration
  initial := Initial program entry
  step := Step program
  final configuration result := configuration.control = .done result
  fault configuration := ¬ WorldWellFormed configuration.machine.world

structure CoreCorrect (program : CoreProgram) (entry : DeclId) : Prop where
  declarations : ProgramWellFormed program.source
  nonvacuous : ∃ initial, Initial program entry initial
  invariant : Glorious.Proof.Invariant (CoreSystem program entry) (fun state => WorldWellFormed state.machine.world)
  progress : (CoreSystem program entry).Safe
  resultType : ∀ initial events final value function,
    Initial program entry initial → (CoreSystem program entry).Steps initial events final →
    final.control = .done (.returned value) → function ∈ program.functions → function.declaration = entry →
    Subtype program.source [] value.type function.signature.output
  exits : ∀ initial events final value,
    Initial program entry initial → (CoreSystem program entry).Steps initial events final →
    final.control = .done (.returned value) →
    ∃ world, ExitDisposition final.machine.world world (final.machine.world.slots.map (·.declaration.id)) [value] .normalReturn

end Glorious.Semantics.Spec
