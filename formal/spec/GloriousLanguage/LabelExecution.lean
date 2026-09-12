import GloriousLanguage.Contracts
import GloriousLanguage.ControlContextTyping
import GloriousLanguage.PatternContextTyping
import GloriousLanguage.SourceAddress

/-! A label request is consumed by actual leave or actual resource exhaustion.
The selected delimiter retains its source result derivation. Payload storage
keeps its actual type: source subtyping is carried as source evidence, not
replaced by a synthetic equality or an assumed typed successful endpoint. -/
namespace Glorious.Language

/-- The source label which produced this exact runtime-closed frame. The
branded label value and saved result close through the same instantiation.
There is no independent frame matcher or result-type reconstruction. -/
def Typing.InstalledLabelTyped (program : Kernel.Program) (world : World)
    (runtime : Execution.Context) (brand region : Identity) (type : Term) : Prop :=
  ∃ source lexical sourceRegion result body,
    Typing.ContextBindingsTyped program world source runtime ∧
    Typing.CodeType program source (.label lexical sourceRegion result body) result ∧
    runtime.term result = type ∧
    (runtime.bindBrand lexical (.label brand)).term
      (.label (.scopedBrand lexical) (.scopedRegion sourceRegion) result) =
      .label (.runtimeBrand (.label brand)) (.runtimeRegion region) type

/-- Bottom elimination may change the surrounding expression result, but it
cannot change the result annotation of the actual source label constructor. -/
theorem Typing.CodeType.label_structure {program : Kernel.Program} {source : Typing.Context}
    {lexical sourceRegion : Identity} {result output : Term} {code body : Kernel.Code}
    (typed : Typing.CodeType program source code output)
    (selected : code = .label lexical sourceRegion result body) :
    sourceRegion ∈ source.static.scope.regions ∧ source.static.scope.currentRegion = some sourceRegion ∧
      lexical ∉ source.static.scope.brands ∧ result.Scoped source.static.scope ∧
      Typing.CodeType program
        { source.bindBrand lexical with labels := (lexical,.scopedRegion sourceRegion,result) :: source.labels } body result := by
  have shape : match (generalizing := false) code with
      | .label lexical region result body =>
          region ∈ source.static.scope.regions ∧ source.static.scope.currentRegion = some region ∧
          lexical ∉ source.static.scope.brands ∧ result.Scoped source.static.scope ∧
          Typing.CodeType program
            { source.bindBrand lexical with labels := (lexical,.scopedRegion region,result) :: source.labels } body result
      | _ => True := by
    refine Typing.CodeType.rec
      (motive_1 := fun source code _ _ => match (generalizing := false) code with
        | .label lexical region result body =>
            region ∈ source.static.scope.regions ∧ source.static.scope.currentRegion = some region ∧
            lexical ∉ source.static.scope.brands ∧ result.Scoped source.static.scope ∧
            Typing.CodeType program
              { source.bindBrand lexical with labels := (lexical,.scopedRegion region,result) :: source.labels } body result
        | _ => True)
      (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    all_goals intros
    all_goals first
    | assumption
    | exact True.intro
    | exact ⟨by assumption,by assumption,by assumption,by assumption,by assumption⟩
  simpa only [selected] using shape

/-- The ordinary local label producer establishes the source/frame relation.
Source region selection and result closing are the existing labelStep proof,
not extra successful-execution admission. -/
theorem Typing.ContextBindingsTyped.label_frame_step {program : Kernel.Program} {before : Execution.State}
    {source : Typing.Context} {runtime : Execution.Context}
    {lexical sourceRegion : Identity} {result output : Term} {body : Kernel.Code}
    (bindings : Typing.ContextBindingsTyped program before.world source runtime)
    (sourceTyped : Typing.CodeType program source (.label lexical sourceRegion result body) output)
    (running : before.task = .run runtime (.label lexical sourceRegion result body)) :
    ∃ region,
      let inner := runtime.bindBrand lexical (.label before.nextBrand)
      Execution.LocalStep program before none
        { before with
          task := .run inner body
          frames := .label runtime before.nextBrand region (runtime.term result) :: before.frames
          nextBrand := before.nextBrand+1 } ∧
      Typing.InstalledLabelTyped program before.world runtime before.nextBrand region (runtime.term result) ∧
      Typing.ContextBindingsTyped program before.world
        { source.bindBrand lexical with labels := (lexical,.scopedRegion sourceRegion,result) :: source.labels } inner := by
  obtain ⟨present,current,fresh,admitted,bodyTyped⟩ := sourceTyped.label_structure rfl
  have origin : Typing.CodeType program source (.label lexical sourceRegion result body) result :=
    .label present current fresh admitted bodyTyped
  obtain ⟨region,step,innerTyped,closed⟩ := bindings.labelStep present fresh admitted running
  exact ⟨region,step,⟨source,lexical,sourceRegion,result,body,bindings,origin,rfl,closed⟩,innerTyped⟩

namespace Execution

/-- Successful leave preserves the exact resident and obtains its owned home
through actual Protect. The source place derivation, its runtime location and
the actual payload resident supply the physical payload type; no post-state
type, transfer, allocation or requested address type is an input. -/
theorem ControlStep.leave_source_result {program : Kernel.Program} {before after : State}
    {caller target : Context} {brand region : Identity} {argument : ResolvedPlace}
    {inner outer : List Frame} {type actual : Term}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (pending : before.task = .leave caller brand argument)
    (route : LabelRoute before.frames brand inner target region type outer)
    (label : Typing.InstalledLabelTyped program before.world target brand region type)
    {placeSource : Typing.Context} {place : Kernel.Place} {writable : Bool}
    (bindings : Typing.ContextBindingsTyped program before.world placeSource caller)
    (interpreted : Typing.SourceInterpreted program.declarations caller placeSource.static)
    (representation : Typing.TargetRepresentation program before.world caller)
    (argumentTyped : Typing.PlaceType program.declarations placeSource place actual writable)
    (resolved : Kernel.ResolvesPlace before.world caller.environment place argument.address argument.authority)
    (step : ControlStep program before none after) :
    ∃ kept value roots source result,
      after.frames = outer ∧
      after.task = .cleanup caller roots (CloseRegions (inner.flatMap Frame.ownedRegions) (.yield target kept)) ∧
      before.world.Stores argument.address value ∧ after.world.Stores kept value ∧ value.Initialized ∧
      Typing.ValueTyped program after.world value ∧
      DefinitionallyEqual program.declarations caller.static value.type (caller.term actual) ∧
      value.ResourcesAccessible program after.world .owned ∧ Permitted after.world .owner .owned kept ∧
      Typing.ContextBindingsTyped program after.world source target ∧ result.Scoped source.static.scope ∧
      target.term result = type ∧ AbandonedRoots after.world inner [kept.root] roots ∧
      Cancelable program after.world roots := by
  cases step <;> try { simp_all only [reduceCtorEq] }
  case leave actualPending actualRoute handoff selected allowed =>
    have conversion : Typing.SourceConversionClosed program.declarations placeSource.static caller :=
      interpreted.sourceConversionClosed
    obtain ⟨rfl,rfl,rfl⟩ := Task.leave.inj (actualPending.symm.trans pending)
    obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := actualRoute.functional route
    have original := handoff
    obtain ⟨value,_,stored,_,_⟩ := original
    obtain ⟨source,lexical,sourceRegion,result,body,contextTyped,sourceTyped,closedLabel,_⟩ := label
    have derived := Typing.ContextBindingsTyped.place_addressTyped valid inventory typed conversion
      representation bindings argumentTyped resolved stored
    have valueAgrees := Typing.AddressTyped.resident_type valid inventory typed derived stored
    have movedTyped := handoff.worldTyped valid inventory typed
    obtain ⟨kept,initialized,resources,permission⟩ := handoff.handed_off typed.1 stored
    exact ⟨_,value,_,source,result,rfl,rfl,stored,kept,initialized,
      World.stores_typed movedTyped.roots kept,valueAgrees,resources,permission,
      handoff.contextBindingsTyped typed contextTyped,sourceTyped.result_scoped,closedLabel,selected,allowed⟩

end Execution

namespace Contracts

open Kernel Execution

/-- The invocation's public interface observation ends at the real outward
label. Its caller-side success or resource failure extends that same machine
run without rewriting the request's label outcome or its callee event trace. -/
theorem ObservationAt.label_caller_step {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {boundary : InvocationBoundary} {start before after : State}
    {request : Observation} {brand : Identity} {argument : ResolvedPlace} {event : Option Event}
    (observed : ObservationAt program host function boundary start before request)
    (outcome : request.outcome = .label brand argument)
    (step : ControlStep program before event after) :
    Observes program host function request ∧ boundary.OutwardLabel before brand argument ∧
      Run program host start (request.events ++ event.toList) after := by
  have outward := observed.2.2.2.2
  rw [outcome] at outward
  refine ⟨⟨boundary,start,before,observed⟩,outward,?_⟩
  have actual : Step program host before event after := Or.inr (Or.inr (Or.inr (Or.inl step)))
  apply observed.2.2.1.execution.append
  cases event with
  | none => exact .silent actual .refl
  | some event => exact .visible actual .refl

/-- General source-compatible label consumption. Source PlaceType/Subtype are
the actual single-argument derivation; the physical payload typing is derived
from the source place through the actual resolution, the world target
representation and the runtime closing law. This theorem does not assume a
successful Protect, a typed output, a requested address type, or a runtime
Subtype after erasing the source assumptions. -/
theorem MayTransfer.source_execution {program : Kernel.Program} {state : State} {boundary : InvocationBoundary}
    {caller target : Execution.Context} {brand region : Identity} {argument : ResolvedPlace}
    {inner outer : List Frame} {type actual expected : Term} {source : Typing.Context}
    {place : Place} {writable : Bool}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program state.world) (transfer : MayTransfer program state boundary)
    (pending : state.task = .leave caller brand argument)
    (route : LabelRoute state.frames brand inner target region type outer)
    (label : Typing.InstalledLabelTyped program state.world target brand region type)
    (sourceTyped : Typing.ContextBindingsTyped program state.world source caller)
    (interpreted : Typing.SourceInterpreted program.declarations caller source.static)
    (representation : Typing.TargetRepresentation program state.world caller)
    (argumentTyped : Typing.PlaceType program.declarations source place actual writable)
    (subtype : Subtype program.declarations source.static actual expected)
    (resolved : ResolvesPlace state.world caller.environment place argument.address argument.authority)
    (selectedType : caller.term expected = type)
    (callerPermission : boundary.LabelCallerPermission program state brand argument) :
    ∃ after event, ControlStep program state event after ∧ Typing.WorldTyped program after.world ∧
      Typing.PlacesType program.declarations source [place] [expected] ∧
      Typing.ContextBindingsTyped program after.world source caller ∧
      ((event = some (.fatal .resource) ∧ after = { state with task := .fatal .resource }) ∨
       ∃ kept value roots targetSource result,
        event = none ∧ after.frames = outer ∧
        after.task = .cleanup caller roots (CloseRegions (inner.flatMap Frame.ownedRegions) (.yield target kept)) ∧
        ResolvesPlace state.world caller.environment place argument.address argument.authority ∧
        state.world.Stores argument.address value ∧ after.world.Stores kept value ∧ value.Initialized ∧
        Typing.ValueTyped program after.world value ∧
        DefinitionallyEqual program.declarations caller.static value.type (caller.term actual) ∧
        Subtype program.declarations source.static actual expected ∧ caller.term expected = target.term result ∧
        value.ResourcesAccessible program after.world .owned ∧ Permitted after.world .owner .owned kept ∧
        Typing.ContextBindingsTyped program after.world targetSource target ∧ result.Scoped targetSource.static.scope ∧
        target.term result = type ∧ AbandonedRoots after.world inner [kept.root] roots ∧
        Cancelable program after.world roots) ∧
      ∀ host function start request, ObservationAt program host function boundary start state request →
        request.outcome = .label brand argument →
        Observes program host function request ∧ boundary.OutwardLabel state brand argument ∧
          Run program host start (request.events ++ event.toList) after := by
  obtain ⟨actualBrand,actualArgument,outward,ready⟩ := transfer
  obtain ⟨context,actualPending⟩ := outward.1
  obtain ⟨rfl,rfl,rfl⟩ := Task.leave.inj (actualPending.symm.trans pending)
  obtain ⟨after,event,step,afterTyped,outcome⟩ :=
    ready.execute valid inventory typed outward.2 pending callerPermission
  refine ⟨after,event,step,afterTyped,.cons ⟨actual,writable,argumentTyped,subtype⟩ .nil,
    step.contextBindingsTyped valid inventory typed sourceTyped,?_,
    fun _ _ _ _ observed outcome => observed.label_caller_step outcome step⟩
  rcases outcome with rfl | fatal
  · right
    obtain ⟨kept,value,roots,targetSource,result,frames,task,original,stored,initialized,valueTyped,valueType,
      resources,permission,targetTyped,admittedResult,closed,selected,allowed⟩ :=
      step.leave_source_result valid inventory typed pending route label sourceTyped interpreted
        representation argumentTyped resolved
    exact ⟨kept,value,roots,targetSource,result,rfl,frames,task,resolved,original,stored,initialized,valueTyped,valueType,
      subtype,selectedType.trans closed.symm,resources,permission,targetTyped,admittedResult,closed,selected,allowed⟩
  · exact Or.inl fatal

end Contracts
end Glorious.Language
