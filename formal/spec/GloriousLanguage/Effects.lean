import GloriousLanguage.Relocation

/-! Deep algebraic handlers, exact operation identity, linear suspension
authority and terminal cleanup. A clause is deliberately outside the
delimiter it services. No rule equates terminal transfer with process abort. -/
namespace Glorious.Language.Execution

open Kernel

def ArmAccepts (program : Kernel.Program) (world : World) (context : Language.Context)
    (operation : DeclId) (arguments : List Term) (payload : List ResolvedPlace) (arm : OperationArm) : Prop :=
  arm.operation = operation ∧ ListRel (Equal program.declarations context) arguments arm.arguments ∧
  ListRel (fun source pattern => Permitted world source.authority .shared source.address ∧
    Matches program.declarations world source.address pattern) payload arm.patterns

def SelectsOperation (program : Kernel.Program) (world : World) (handler : InstalledHandler)
    (operation : DeclId) (arguments : List Term) (payload : List ResolvedPlace) (arm : OperationArm) : Prop :=
  ∃ skipped rest,
    handler.syntaxNode.operations = skipped ++ arm :: rest ∧
    ArmAccepts program world handler.environment.static operation arguments payload (arm.closeHead handler.environment.instantiation) ∧
    ∀ earlier ∈ skipped, ¬ ArmAccepts program world handler.environment.static operation arguments payload (earlier.closeHead handler.environment.instantiation)

def Bypasses (program : Kernel.Program) (world : World) (operation : DeclId)
    (arguments : List Term) (payload : List ResolvedPlace) : Frame → Prop
  | .handler handler _ => ¬ ∃ arm, SelectsOperation program world handler operation arguments payload arm
  | .foreign _ | .hostCallback .. => False
  | _ => True

def Routes (program : Kernel.Program) (before : State) (operation : DeclId)
    (arguments : List Term) (payload : List ResolvedPlace) (inner : List Frame) (handler : InstalledHandler)
    (owns : Bool) (arm : OperationArm) (outer : List Frame) : Prop :=
  before.frames = inner ++ .handler handler owns :: outer ∧
  (∀ frame ∈ inner, Bypasses program before.world operation arguments payload frame) ∧
  SelectsOperation program before.world handler operation arguments payload arm

def FrameOwns (frame : Frame) (root : Root) : Prop :=
  match frame with
  | .activation _ activation _ => OwnedByActivation root activation
  | .scope context scope _ => OwnedByScope root context.activation scope
  | .handler handler owns =>
      OwnedByScope root handler.computation.activation handler.computation.scope ∨
      (owns = true ∧ OwnedByActivation root handler.environment.activation)
  | .serviced handler owns clause _ | .completion handler owns clause =>
      OwnedByActivation root clause.activation ∨ (owns = true ∧ OwnedByActivation root handler.environment.activation)
  | _ => False

def DelimitedRoots (world : World) (handler : InstalledHandler) (inner : List Frame)
    (kept roots : List Identity) : Prop :=
  NewestFirst world roots ∧ ∀ id, id ∈ roots ↔ ∃ root,
    world.roots.get id = some root ∧ root.live = true ∧ id ∉ kept ∧
    (OwnedByScope root handler.computation.activation handler.computation.scope ∨ ∃ frame ∈ inner, FrameOwns frame root)

def SaveHomes (world : World) (roots : List Identity) (homes : Table Home) : Prop :=
  homes = (world.roots.filter (fun entry => entry.1 ∈ roots)).map (fun (id,root) => (id,root.home))

def suspendRoots (world : World) (roots : List Identity) (continuation : Identity) : World :=
  { world with roots := world.roots.map (fun (id,root) => (id,if id ∈ roots then { root with home := .suspended continuation } else root)) }

def restoreRoots (world : World) (homes : Table Home) : World :=
  { world with roots := world.roots.map (fun (id,root) => (id,{ root with home := (homes.get id).getD root.home })) }

inductive RetiresEmpty : World → List Address → World → Prop where
  | nil {world} : RetiresEmpty world [] world
  | cons {before address addresses middle after} : address.fields = [] → Retires before address.root middle →
      RetiresEmpty middle addresses after → RetiresEmpty before (address :: addresses) after

def CaptureLocals (captures : List Capture) : List Local :=
  captures.map (fun capture => ⟨capture.formal,capture.type,false⟩)

def Installs (program : Kernel.Program) (before : State) (outer : Context) (syntaxNode : Handler)
    (handler : InstalledHandler) (after : World) : Prop :=
  ∃ first second sources captures captured bindings bound disposed,
    FreshRegion before.world before.world.nextRegion first ∧ FreshRegion first first.nextRegion second ∧
    captures = syntaxNode.captures.map (Capture.mapTerms outer.term) ∧
    Captures program outer second captures sources captured ∧
    BindsInputs program.declarations before.nextActivation before.world.nextRegion before.world.nextRegion captured
      ((CaptureLocals captures).zip sources |>.map (fun (localSlot,address) => ⟨.capture 0,localSlot,address,.owner,.owned⟩)) bindings bound ∧
    RetiresEmpty bound sources disposed ∧ after = disposed ∧
    handler = ⟨before.nextHandler,syntaxNode,
      ⟨bindings,outer.module,before.nextActivation,before.world.nextRegion,before.world.nextRegion,outer.instantiation,outer.unsafeAllowed⟩,
      { outer with scope := first.nextRegion, region := first.nextRegion },outer⟩

def StartsClause (before : State) (handler : InstalledHandler) (context : Context) (after : World) : Prop :=
  FreshRegion before.world before.world.nextRegion after ∧
  context = { handler.environment with activation := before.nextActivation, scope := before.world.nextRegion, region := before.world.nextRegion }

def StartsResumptionClause (before : State) (handler : InstalledHandler) (lexical : Local)
    (context : Context) (localSlot : Local) (after : World) : Prop :=
  ∃ outer brand,
    StartsClause before handler outer after ∧
    lexical.resumptionBrand = some brand ∧
    context = outer.bindBrand brand (.resumption before.nextContinuation) ∧
    localSlot = context.local lexical

inductive PayloadPlan (program : Language.Program) (world : World) :
    List Address → List Pattern → PatternActions → Prop where
  | nil : PayloadPlan program world [] [] ⟨[],[],[]⟩
  | cons {address addresses pattern patterns actions rest} :
      PatternPlan program world address .owner .owned pattern actions → PayloadPlan program world addresses patterns rest →
      PayloadPlan program world (address :: addresses) (pattern :: patterns)
        ⟨actions.shells ++ rest.shells,actions.bindings ++ rest.bindings,rest.cleanup ++ actions.cleanup⟩

def CreatesContinuation (program : Kernel.Program) (context : Context) (before : World)
    (id : Identity) (signature : Signature) (answer effects : Term) (quantity : Quantity)
    (localSlot : Local) (address : Address) (after : World) : Prop :=
  ∃ allocated layout,
    localSlot.type = .continuation (.runtimeBrand (.resumption id)) signature.result answer effects quantity ∧
    Allocates program.declarations before (.localSlot context.activation context.scope) context.region
      localSlot.type layout localSlot.mutable address allocated ∧
    NewValue program.declarations allocated address localSlot.type (.continuation id) [] after

def ActiveObligation (suspension : Suspension) : Prop :=
  suspension.active = true ∧ suspension.original = true ∧
  suspension.quantity.SurfaceResumption ∧
  suspension.quantity.upper = some (suspension.remaining + suspension.used)

def SuspendPermission (program : Kernel.Program) (world : World) (roots : List Identity)
    (quantity : Quantity) (frames : List Frame) : Prop :=
  quantity.SurfaceResumption ∧ Suspensible world roots ∧
  (quantity.lower = 0 → Cancelable program.declarations world roots) ∧
  (∀ n, quantity.upper = some n → 1 < n → Replayable program.declarations world roots ∧ ∀ frame ∈ frames, SnapshotFrame frame)

def SuspensionRegions (suspension : Suspension) : List Identity :=
  (suspension.frames.flatMap Frame.ownedRegions ++ [suspension.handler.computation.region]).eraseDups

/-- Checked after clause-local destruction, so disposing an optional handle
can perform its cancellation. Missing suspension state is not a spent token. -/
def ClauseSettled (state : State) : Option Identity → Prop
  | none => True
  | some id => ∃ suspension, state.resumptions.get id = some suspension ∧
      suspension.quantity.Contains suspension.used ∧ suspension.active = false

inductive EffectStep (program : Kernel.Program) : State → Option Event → State → Prop where
  | install {before context id computation syntaxNode handler after} :
      before.task = .run context (.handle id computation syntaxNode) → Installs program before context syntaxNode handler after →
      EffectStep program before none { before with world := after, task := .run handler.computation computation, frames := .handler handler true :: before.frames, nextActivation := before.nextActivation+1, nextHandler := before.nextHandler+1 }
  | operationCall {before context call receiver authority value id arguments operation signature payload} :
      before.task = .apply context call false → call.environment = none →
      ResolvesPlace before.world context.environment call.callee receiver authority →
      before.world.Stores receiver value → value.head = .operation id arguments →
      Permitted before.world authority .shared receiver → OperationInstance program id arguments operation signature →
      signature = call.signature → ResolvedOperands before.world context.environment call.arguments payload →
      EffectStep program before (some (.perform id arguments)) { before with task := .perform context id arguments payload }
  | terminal {before context id arguments payload inner handler owns arm outer operation signature clause withRegion
      kept moved roots actions} : before.task = .perform context id arguments payload →
      OperationInstance program id arguments operation signature → operation.terminal = true → arm.continuation = none →
      Routes program before id arguments payload inner handler owns arm outer → StartsClause before handler clause withRegion →
      Protects program clause withRegion payload kept moved →
      DelimitedRoots moved handler inner (kept.map Address.root) roots → Cancelable program.declarations moved roots →
      PayloadPlan program.declarations moved kept (arm.patterns.map (Pattern.mapTerms clause.term)) actions →
      EffectStep program before none { before with world := moved, task := .cleanup context roots (CloseRegions (inner.flatMap Frame.ownedRegions ++ [handler.computation.region]) (.pattern clause (ScheduledPattern actions) arm.body)), frames := .serviced handler owns clause none :: outer, nextActivation := before.nextActivation+1 }
  | suspend {before context id arguments payload inner handler owns arm outer operation signature quantity bound
      clause withRegion kept moved roots homes lexical localSlot address created actions suspension} :
      before.task = .perform context id arguments payload → OperationInstance program id arguments operation signature →
      operation.terminal = false → operation.quantity = some quantity → quantity.upper = some bound →
      arm.continuation = some lexical → Routes program before id arguments payload inner handler owns arm outer →
      StartsResumptionClause before handler lexical clause localSlot withRegion → Protects program clause withRegion payload kept moved →
      DelimitedRoots moved handler inner (kept.map Address.root) roots →
      SuspendPermission program moved roots quantity inner → SaveHomes moved roots homes →
      CreatesContinuation program clause (suspendRoots moved roots before.nextContinuation) before.nextContinuation
        signature (clause.term handler.syntaxNode.result) signature.effects quantity localSlot address created →
      PayloadPlan program.declarations created kept (arm.patterns.map (Pattern.mapTerms clause.term)) actions →
      suspension = ⟨before.nextContinuation,handler,inner,context,roots,homes,moved.nextRoot,quantity,bound,0,true,true⟩ →
      EffectStep program before (some (.suspend before.nextContinuation)) { before with world := created, task := .pattern (clause.bind localSlot address) (ScheduledPattern actions) arm.body, frames := .serviced handler owns clause (some before.nextContinuation) :: outer, resumptions := before.resumptions.set before.nextContinuation suspension, nextContinuation := before.nextContinuation+1, nextActivation := before.nextActivation+1 }
  | suspendTailArm {before context id arguments payload inner handler owns arm outer operation signature quantity bound
      clause withRegion kept moved roots homes actions suspension} :
      before.task = .perform context id arguments payload → OperationInstance program id arguments operation signature →
      operation.terminal = false → operation.quantity = some quantity → quantity.upper = some bound → quantity.Contains 1 →
      arm.continuation = none → Routes program before id arguments payload inner handler owns arm outer →
      StartsClause before handler clause withRegion → Protects program clause withRegion payload kept moved →
      DelimitedRoots moved handler inner (kept.map Address.root) roots →
      SuspendPermission program moved roots quantity inner → SaveHomes moved roots homes →
      PayloadPlan program.declarations moved kept (arm.patterns.map (Pattern.mapTerms clause.term)) actions →
      suspension = ⟨before.nextContinuation,handler,inner,context,roots,homes,moved.nextRoot,quantity,bound,0,true,true⟩ →
      EffectStep program before (some (.suspend before.nextContinuation)) { before with world := suspendRoots moved roots before.nextContinuation, task := .pattern clause (ScheduledPattern actions) arm.body, frames := .tailResume clause before.nextContinuation :: .serviced handler owns clause (some before.nextContinuation) :: outer, resumptions := before.resumptions.set before.nextContinuation suspension, nextContinuation := before.nextContinuation+1, nextActivation := before.nextActivation+1 }
  | continuationCall {before context call tail receiver authority value id argument permission} :
      before.task = .apply context call tail → call.environment = none →
      ResolvesPlace before.world context.environment call.callee receiver authority →
      before.world.Stores receiver value → value.head = .continuation id → Permitted before.world authority .shared receiver →
      (∃ place, call.arguments = [place] ∧ ResolvesPlace before.world context.environment place argument permission) →
      EffectStep program before none { before with task := .resume context id ⟨argument,permission⟩ tail }
  | tailArmReturn {before context value caller id rest} : before.task = .yield context value →
      before.frames = .tailResume caller id :: rest →
      EffectStep program before none { before with task := .resume caller id ⟨value,.owner⟩ false, frames := rest }
  | resumeLast {before caller id argument suspension after kept transferred} :
      before.task = .resume caller id argument false → before.resumptions.get id = some suspension →
      ActiveObligation suspension → suspension.remaining = 1 →
      after = restoreRoots before.world suspension.homes →
      Protect program suspension.context after argument.address argument.authority kept transferred →
      EffectStep program before (some (.replay id true)) { before with world := transferred, task := .yield suspension.context kept, frames := suspension.frames ++ [.handler suspension.handler false,.resumed caller] ++ before.frames, resumptions := before.resumptions.set id { suspension with remaining := 0, used := suspension.used+1, active := false } }
  | resumeCopy {before caller id argument suspension map copied kept transferred} :
      before.task = .resume caller id argument false → before.resumptions.get id = some suspension →
      ActiveObligation suspension → 1 < suspension.remaining → CopiesSnapshot program before suspension map copied →
      Protect program (map.context suspension.context) copied.world argument.address argument.authority kept transferred →
      EffectStep program before (some (.replay id false)) { copied with world := transferred, task := .yield (map.context suspension.context) kept, frames := suspension.frames.map map.frame ++ [.handler (map.installed suspension.handler) false,.resumed caller] ++ before.frames, resumptions := before.resumptions.set id { suspension with remaining := suspension.remaining-1, used := suspension.used+1 } }
  | resumeReturns {before context value caller rest kept after} : before.task = .yield context value →
      before.frames = .resumed caller :: rest → Protect program caller before.world value .owner kept after →
      EffectStep program before none { before with world := after, frames := rest, task := .retire value.root (.yield caller kept) }
  | completionIdentity {before context value handler owns rest clause withRegion kept after roots} :
      before.task = .yield context value → before.frames = .handler handler owns :: rest →
      handler.syntaxNode.completion = [] → StartsClause before handler clause withRegion →
      Protect program clause withRegion value .owner kept after →
      ScopeRoots after handler.computation.activation handler.computation.scope [] roots → Suspensible after roots →
      EffectStep program before none { before with world := after, task := .cleanup context roots (.closeRegion handler.computation.region (.yield clause kept)), frames := .completion handler owns clause :: rest, nextActivation := before.nextActivation+1 }
  | completion {before context value handler owns rest clause withRegion kept after roots arm actions} :
      before.task = .yield context value → before.frames = .handler handler owns :: rest →
      StartsClause before handler clause withRegion → Protect program clause withRegion value .owner kept after →
      ScopeRoots after handler.computation.activation handler.computation.scope [] roots → Suspensible after roots →
      FirstArm program.declarations after kept handler.syntaxNode.completion arm →
      PatternPlan program.declarations after kept .owner .owned (arm.pattern.mapTerms clause.term) actions →
      EffectStep program before none { before with world := after, task := .cleanup context roots (.closeRegion handler.computation.region (.pattern clause (ScheduledPattern actions) arm.body)), frames := .completion handler owns clause :: rest, nextActivation := before.nextActivation+1 }
  | completed {before context value handler owns clause rest kept after roots} :
      before.task = .yield context value → before.frames = .completion handler owns clause :: rest →
      context.activation = clause.activation →
      Protect program (if owns then handler.outer else handler.environment) before.world value .owner kept after →
      ActivationRoots after clause.activation [] roots → Suspensible after roots →
      EffectStep program before none { before with world := after, frames := rest, task := .cleanup context roots (.closeRegion clause.region (.finishClause handler owns none kept)) }
  | serviced {before context value handler owns clause id rest kept after roots} :
      before.task = .yield context value → before.frames = .serviced handler owns clause id :: rest →
      context.activation = clause.activation →
      Protect program (if owns then handler.outer else handler.environment) before.world value .owner kept after →
      ActivationRoots after clause.activation [] roots → Suspensible after roots →
      EffectStep program before none { before with world := after, frames := rest, task := .cleanup context roots (.closeRegion clause.region (.finishClause handler owns id kept)) }
  | finishedOwnedClause {before handler id value roots} : before.task = .finishClause handler true id value →
      ClauseSettled before id → ActivationRoots before.world handler.environment.activation [] roots →
      Suspensible before.world roots →
      EffectStep program before none { before with task := .cleanup handler.environment roots (.closeRegion handler.environment.region (.yield handler.outer value)) }
  | finishedLentClause {before handler id value} : before.task = .finishClause handler false id value →
      ClauseSettled before id →
      EffectStep program before none { before with task := .yield handler.environment value }
  | disposeContinuation {before context address authority next value id suspension cleared} :
      before.task = .destroy context address authority next → before.world.Stores address value → value.head = .continuation id →
      Permitted before.world authority .owned address → before.resumptions.get id = some suspension →
      before.world.write address none = some cleared →
      EffectStep program before (some (.destroy address value.owner)) { before with world := cleared, task := if suspension.active then .cancel context id next else next }
  | cancel {before context id next suspension} : before.task = .cancel context id next →
      before.resumptions.get id = some suspension → ActiveObligation suspension → suspension.quantity.lower = 0 →
      Cancelable program.declarations before.world suspension.roots →
      EffectStep program before (some (.cancel id)) { before with world := restoreRoots before.world suspension.homes, task := .cleanup context suspension.roots (CloseRegions (SuspensionRegions suspension) next), resumptions := before.resumptions.set id { suspension with active := false, remaining := 0 } }

theorem exact_resumption_not_cancelable {program : Kernel.Program} {before after : State}
    {id suspension}
    (found : before.resumptions.get id = some suspension)
    (positive : 0 < suspension.quantity.lower) : ¬ EffectStep program before (some (.cancel id)) after := by
  intro step
  cases step <;> simp_all

end Glorious.Language.Execution
