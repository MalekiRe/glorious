import GloriousLanguage.BindingPersistence
import GloriousLanguage.PredicateScope
import GloriousLanguage.InvocationInputs

/-! The source body's one local environment is related to the actual runtime
environment. Entry constructs this relation from input recipes, fresh scope
installation and sequential binding; no typed output context is assumed. -/
namespace Glorious.Language

theorem Typing.CodeType.result_scoped {program : Kernel.Program} {context : Typing.Context}
    {code : Kernel.Code} {result : Term} (typed : Typing.CodeType program context code result) :
    result.Scoped context.static.scope := by
  refine Typing.CodeType.rec
    (motive_1 := fun context _ result _ => result.Scoped context.static.scope)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  all_goals intros
  all_goals first
  | assumption
  | exact True.intro
  | exact (‹Typing.TermsScoped _ _›) _ List.mem_cons_self
  | exact (‹Typing.TermsScoped _ _›) _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem Typing.FunctionType.locals_nodup {program : Kernel.Program} {function : Kernel.Function}
    (typed : Typing.FunctionType program function) :
    ((function.captures ++ function.parameters).map (·.id)).Nodup := by
  obtain ⟨_,_,_,parameters,captures,separate,_,_⟩ := typed
  rw [List.map_append,List.nodup_append]
  refine ⟨captures,parameters,?_⟩
  intro first member second present same
  obtain ⟨capture,inCaptures,rfl⟩ := List.mem_map.mp member
  obtain ⟨formal,inFormals,rfl⟩ := List.mem_map.mp present
  exact separate formal inFormals capture inCaptures same.symm

/-- The actual source-body admission already covers its complete signature
predicate projection. Entry consumes that same evidence for assumptions, not
an additional output-context certificate or a second predicate analysis. -/
theorem Typing.FunctionType.assumptions_scoped {program : Kernel.Program} {function : Kernel.Function}
    (typed : Typing.FunctionType program function) (module : ModuleId) :
    (Typing.FunctionContext function module).static.AssumptionsScoped := by
  obtain ⟨_,_,_,_,_,_,admitted,_⟩ := typed
  intro constraint member term present
  have nested : term ∈ function.signature.constraints.flatMap Constraint.terms := List.mem_flatMap.mpr ⟨constraint,member,present⟩
  exact (admitted term (by
    simp only [Signature.terms,List.mem_append,List.mem_cons,nested,true_or,or_true])).scoped _

theorem Kernel.Instance.locals_scopeClosed {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    (inventory : Kernel.BodyInventory program) {id : DeclId} {arguments : List Term} {function : Kernel.Function}
    (selected : Kernel.Instance program id arguments function) (typed : Typing.FunctionType program function) :
    ∀ localSlot ∈ function.captures ++ function.parameters, localSlot.type.ScopeClosed := by
  have closed := selected.scopeClosed valid inventory
  obtain ⟨_,_,parameters,_⟩ := typed
  intro localSlot member
  rcases List.mem_append.mp member with capture | parameter
  · exact closed.2.2 localSlot capture
  · apply closed.1
    rw [← parameters]
    exact List.mem_map.mpr ⟨localSlot,parameter,rfl⟩

namespace Execution

theorem ArgumentInputs.resident_formals {world : World} {context : Context} {function : Kernel.Function}
    {places : List Kernel.Place} {inputs : List Kernel.InvocationInput}
    (selected : ArgumentInputs world context 0 function.parameters places inputs)
    (receiver : ResolvedPlace) (access : Access) : (EntrySource.resident receiver access inputs).HasFormals function :=
  selected.formals

theorem ReservationInputs.formals {world : World} {available : Availability} {access : Access}
    {formals : List Kernel.Local} {inputs : List Kernel.InvocationInput}
    (selected : ReservationInputs world available access formals inputs) : inputs.map (·.formal) = formals := by
  rw [selected.2.2.1]
  simp only [List.map_map,Function.comp_def]
  calc
    _ = ((formals.zip available.reserved).zipIdx.map Prod.fst).map Prod.fst := by rw [List.map_map]; rfl
    _ = (formals.zip available.reserved).map Prod.fst := congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 _)
    _ = formals := List.map_fst_zip (Nat.le_of_eq selected.1.symm)

theorem ReservationInputs.contextual_formals {world : World} {context : Context} {function : Kernel.Function}
    {available : Availability} {access : Access} {captures inputs : List Kernel.InvocationInput} {places : List Kernel.Place}
    (selected : ReservationInputs world available access function.captures captures)
    (arguments : ArgumentInputs world context 0 function.parameters places inputs)
    (receiver witness : ResolvedPlace) (receiverAccess witnessAccess : Access) :
    (EntrySource.contextual receiver receiverAccess witness witnessAccess (captures ++ inputs)).HasFormals function := by
  simp only [EntrySource.HasFormals,List.map_append,selected.formals,arguments.formals]

theorem _root_.Glorious.Language.Foreign.CallbackInputs.formals {world : World} {formals : List Kernel.Local}
    {arguments : List ResolvedPlace} {inputs : List Kernel.InvocationInput}
    (selected : Foreign.CallbackInputs world formals arguments inputs) : inputs.map (·.formal) = formals := by
  rw [selected.1]
  simp only [List.map_map,Function.comp_def]
  calc
    _ = ((formals.zip arguments).zipIdx.map Prod.fst).map Prod.fst := by rw [List.map_map]; rfl
    _ = (formals.zip arguments).map Prod.fst := congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 _)
    _ = formals := List.map_fst_zip (Nat.le_of_eq selected.2.length_eq)

theorem _root_.Glorious.Language.Foreign.CallbackInputs.supplied_formals {world : World} {function : Kernel.Function} {receiver : Address}
    {authority : Authority} {access : Access} {arguments : List ResolvedPlace} {captures inputs : List Kernel.InvocationInput}
    (captureInputs : CaptureInputs world receiver authority access function.captures captures)
    (selected : Foreign.CallbackInputs world function.parameters arguments inputs) :
    (EntrySource.supplied (captures ++ inputs)).HasFormals function := by
  simp only [EntrySource.HasFormals,List.map_append,captureInputs.formals,selected.formals]

end Execution

namespace Typing

/-- Scoped declared local storage. Retired whole-root slots retain their
declared type; only a successful runtime read recovers usable value typing.
This does not grant loan permission, active labels or execution progress. -/
structure ContextBindingsTyped (program : Kernel.Program) (world : World)
    (source : Context) (runtime : Execution.Context) : Prop where
  moduleEq : runtime.module = source.static.module
  unsafeEq : runtime.unsafeAllowed = source.static.unsafeAllowed
  covers : runtime.instantiation.Covers source.static.scope
  distinct : (source.locals.map (·.id)).Nodup
  admitted : ∀ localSlot ∈ source.locals, localSlot.type.Scoped source.static.scope
  bindings : ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
    BindingStorageTyped program.declarations world binding.address (runtime.term localSlot.type)) source.locals runtime.environment
  assumptions : source.static.AssumptionsScoped

end Typing

theorem Kernel.Environment.selects_of_nodup {environment : Kernel.Environment} {binding : Kernel.Binding}
    (distinct : (environment.map (·.localSlot)).Nodup) (member : binding ∈ environment) :
    environment.Selects binding.localSlot binding := by
  refine ⟨member,rfl,?_⟩
  intro other present same
  induction environment with
  | nil => cases member
  | cons first rest ih =>
    have separated := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp member with rfl | bindingInRest
    · rcases List.mem_cons.mp present with rfl | otherInRest
      · rfl
      · apply False.elim; apply separated.1
        simpa only [same] using (List.mem_map.mpr ⟨other,otherInRest,rfl⟩ : other.localSlot ∈ rest.map (·.localSlot))
    · rcases List.mem_cons.mp present with rfl | otherInRest
      · apply False.elim; apply separated.1
        simpa only [same] using (List.mem_map.mpr ⟨binding,bindingInRest,rfl⟩ : binding.localSlot ∈ rest.map (·.localSlot))
      · exact ih separated.2 bindingInRest otherInRest

theorem Typing.ContextBindingsTyped.selects {program : Kernel.Program} {world : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program world source runtime)
    {localSlot : Kernel.Local} (member : localSlot ∈ source.locals) :
    ∃ binding, runtime.environment.Selects localSlot.id binding ∧
      Typing.BindingStorageTyped program.declarations world binding.address (runtime.term localSlot.type) := by
  have related := typed.bindings
  have ids : runtime.environment.map (·.localSlot) = source.locals.map (·.id) := by
    generalize source.locals = locals at related ⊢
    generalize runtime.environment = environment at related ⊢
    induction related with
    | nil => rfl
    | cons first _ ih => simp only [List.map_cons,first.1,ih]
  have distinct : (runtime.environment.map (·.localSlot)).Nodup := ids ▸ typed.distinct
  obtain ⟨binding,present,identity,located⟩ := related.member_left member
  exact ⟨binding,identity ▸ Kernel.Environment.selects_of_nodup distinct present,located⟩

theorem Typing.ContextBindingsTyped.read_local {program : Kernel.Program} {world : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program world) (typed : Typing.ContextBindingsTyped program world source runtime)
    {localSlot : Kernel.Local} (member : localSlot ∈ source.locals) {binding : Kernel.Binding} {value : Value}
    (selected : runtime.environment.Selects localSlot.id binding) (stored : world.Stores binding.address value) :
    Typing.ValueTyped program world value ∧ value.type = runtime.term localSlot.type := by
  obtain ⟨actual,found,storage⟩ := typed.selects member
  have same := selected.2.2 actual found.1 found.2.1
  subst actual
  exact (storage.read valid inventory worldTyped stored).2

theorem Typing.ContextBindingsTyped.world {program : Kernel.Program} {before after : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before source runtime)
    (preserved : ∀ address type, Typing.BindingStorageTyped program.declarations before address type →
      Typing.BindingStorageTyped program.declarations after address type) :
    Typing.ContextBindingsTyped program after source runtime := by
  exact ⟨typed.moduleEq,typed.unsafeEq,typed.covers,typed.distinct,typed.admitted,
    typed.bindings.imp (fun _ _ pair => ⟨pair.1,preserved _ _ pair.2⟩),typed.assumptions⟩

/-- Retiring a moved/discarded owner does not remove its lexical declaration
or pretend that the retired address remains readable. -/
theorem Retires.contextBindingsTyped {program : Kernel.Program} {before after : World} {id : Identity}
    (retired : Retires before id after) {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before source runtime) :
    Typing.ContextBindingsTyped program after source runtime :=
  typed.world (fun _ _ binding => retired.bindingStorageTyped binding)

theorem EndsLoan.contextBindingsTyped {program : Kernel.Program} {before after : World} {id : Identity}
    (ended : EndsLoan before id after) {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before source runtime) :
    Typing.ContextBindingsTyped program after source runtime :=
  typed.world (fun _ _ binding => ended.bindingStorageTyped binding)

/-- Every actual close/release transition preserves retained contexts. The
proof consumes their resident invocation guards and the existing EndsLoan
admission, not an externally supplied inequality between loan identities. -/
theorem Execution.LocalStep.loanRelease_contextBindingsTyped {program : Kernel.Program}
    {before after : Execution.State} {event : Option Execution.Event}
    (step : Execution.LocalStep program before event after)
    (releasing : ∃ id next, before.task = .closeLoan id next ∨ before.task = .releaseLoan id next)
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before.world source runtime) :
    Typing.ContextBindingsTyped program after.world source runtime := by
  cases step <;> obtain ⟨id,next,request | request⟩ := releasing
  all_goals simp_all
  all_goals apply EndsLoan.contextBindingsTyped <;> assumption

theorem Execution.AtomStep.contextBindingsTyped {program : Kernel.Program} {before after : Execution.State} {event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world) (step : Execution.AtomStep program before event after)
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before.world source runtime) :
    Typing.ContextBindingsTyped program after.world source runtime :=
  typed.world (fun _ _ binding => step.bindingStorageTyped valid inventory worldTyped binding)

theorem Execution.Captures.contextBindingsTyped {program : Kernel.Program} {before after : World}
    {context : Execution.Context} {captures addresses}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before)
    (captured : Execution.Captures program context before captures addresses after)
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before source runtime) :
    Typing.ContextBindingsTyped program after source runtime :=
  typed.world (fun _ _ binding => captured.bindingStorageTyped valid inventory worldTyped binding)

theorem Execution.Captures.length_eq {program : Kernel.Program} {context : Execution.Context}
    {before after : World} {captures addresses}
    (captured : Execution.Captures program context before captures addresses after) :
    captures.length = addresses.length := by
  induction captured with
  | nil => rfl
  | owned _ _ _ _ _ ih => exact congrArg Nat.succ ih
  | borrowed _ _ _ _ _ _ ih => exact congrArg Nat.succ ih

theorem Typing.ContextBindingsTyped.result_scopeClosed {program : Kernel.Program} {world : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (bindings : Typing.ContextBindingsTyped program world source runtime)
    {code : Kernel.Code} {result : Term} (body : Typing.CodeType program source code result) :
    (runtime.term result).ScopeClosed :=
  runtime.instantiation.closes bindings.covers result body.result_scoped

theorem Typing.ContextBindingsTyped.bind {program : Kernel.Program} {world : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program world source runtime)
    {localSlot : Kernel.Local} {address : Address} {authority : Authority}
    (admitted : localSlot.type.Scoped source.static.scope)
    (located : Typing.BindingStorageTyped program.declarations world address (runtime.term localSlot.type)) :
    Typing.ContextBindingsTyped program world (source.bind localSlot)
      (runtime.bind (runtime.local localSlot) address authority) := by
  refine ⟨typed.moduleEq,typed.unsafeEq,typed.covers,?_,?_,?_,typed.assumptions⟩
  · change (localSlot.id :: (source.locals.filter (fun previous => previous.id != localSlot.id)).map (·.id)).Nodup
    refine List.nodup_cons.mpr ⟨?_,?_⟩
    · intro member
      obtain ⟨previous,present,same⟩ := List.mem_map.mp member
      have different := (List.mem_filter.mp present).2
      simp [same] at different
    · exact typed.distinct.sublist (List.filter_sublist.map Kernel.Local.id)
  · intro previous member
    rcases List.mem_cons.mp member with rfl | present
    · exact admitted
    · exact typed.admitted previous (List.mem_filter.mp present).1
  · apply ListRel.cons ⟨rfl,located⟩
    exact typed.bindings.filter _ _ (fun _ _ pair => by
      simp only [pair.1,Execution.Context.local,Kernel.Local.mapTerms])

theorem Typing.ContextBindingsTyped.bindBrand {program : Kernel.Program} {world : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program world source runtime)
    {lexical : Identity} (fresh : lexical ∉ source.static.scope.brands) (brand : RuntimeBrand) :
    Typing.ContextBindingsTyped program world (source.bindBrand lexical) (runtime.bindBrand lexical brand) := by
  refine ⟨typed.moduleEq,typed.unsafeEq,typed.covers.bindBrand lexical brand,typed.distinct,?_,?_,
    typed.assumptions.bindBrand lexical⟩
  · intro localSlot member
    exact (typed.admitted localSlot member).mono (fun _ member => member)
      (fun _ member => List.mem_cons_of_mem _ member)
  · have related := typed.bindings
    have admitted := typed.admitted
    change ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
      Typing.BindingStorageTyped program.declarations world binding.address ((runtime.bindBrand lexical brand).term localSlot.type))
      source.locals runtime.environment
    generalize source.locals = locals at related admitted ⊢
    generalize runtime.environment = environment at related ⊢
    induction related with
    | nil => exact .nil
    | @cons localSlot binding locals bindings first rest ih =>
      refine ListRel.cons ⟨first.1,?_⟩ ?_
      · rw [runtime.bindBrand_term fresh (admitted localSlot List.mem_cons_self)]
        exact first.2
      · exact ih (fun localSlot member => admitted localSlot (List.mem_cons_of_mem _ member))

theorem Typing.ContextBindingsTyped.bindRegion {program : Kernel.Program} {world : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program world source runtime)
    {lexical : Identity} (fresh : lexical ∉ source.static.scope.regions) (region : Identity) :
    Typing.ContextBindingsTyped program world (source.bindRegion lexical)
      { runtime.bindRegion lexical region with scope := region, region := region } := by
  refine ⟨typed.moduleEq,typed.unsafeEq,typed.covers.bindRegion lexical region,typed.distinct,?_,?_,
    typed.assumptions.bindRegion lexical⟩
  · intro localSlot member
    exact (typed.admitted localSlot member).mono (fun _ member => List.mem_cons_of_mem _ member)
      (fun _ member => member)
  · have related := typed.bindings
    have admitted := typed.admitted
    change ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
      Typing.BindingStorageTyped program.declarations world binding.address ((runtime.bindRegion lexical region).term localSlot.type))
      source.locals runtime.environment
    generalize source.locals = locals at related admitted ⊢
    generalize runtime.environment = environment at related ⊢
    induction related with
    | nil => exact .nil
    | @cons localSlot binding locals bindings first rest ih =>
      refine ListRel.cons ⟨first.1,?_⟩ ?_
      · change Typing.BindingStorageTyped program.declarations world binding.address ((runtime.bindRegion lexical region).term localSlot.type)
        rw [runtime.bindRegion_term fresh (admitted localSlot List.mem_cons_self)]
        exact first.2
      · exact ih (fun localSlot member => admitted localSlot (List.mem_cons_of_mem _ member))

/-- Both local-bind and suspended evaluation frames use this actual
allocation producer, including its fresh vacant destination. -/
theorem Allocates.contextBindingsTyped {program : Kernel.Program} {before after : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (world : before.WellFormed) (typed : Typing.ContextBindingsTyped program before source runtime)
    {localSlot : Kernel.Local} {address : Address} {layout : Layout}
    (admitted : localSlot.type.Scoped source.static.scope)
    (allocated : Allocates program.declarations before (.localSlot runtime.activation runtime.scope) runtime.region
      (runtime.term localSlot.type) layout localSlot.mutable address after) :
    Typing.ContextBindingsTyped program after (source.bind localSlot)
      (runtime.bind (runtime.local localSlot) address) := by
  exact (typed.world (fun _ _ located => allocated.bindingStorageTyped world located)).bind admitted allocated.created_bindingStorageTyped

theorem Kernel.BindsPattern.contextBindingsTyped {program : Kernel.Program} {before after : World}
    {source : Typing.Context} {runtime : Execution.Context} {localSlot : Kernel.Local}
    {address : Address} {authority : Authority} {access : Access} {binding : Kernel.Binding}
    (worldTyped : Typing.WorldTyped program before)
    (typed : Typing.ContextBindingsTyped program before source runtime)
    (admitted : localSlot.type.Scoped source.static.scope)
    (bound : Kernel.BindsPattern program.declarations runtime.activation runtime.scope runtime.region before
      (runtime.local localSlot) address authority access binding after) :
    Typing.ContextBindingsTyped program after (source.bind localSlot)
      (runtime.bind (runtime.local localSlot) binding.address binding.authority) :=
  (typed.world (fun _ _ storage => bound.preserves_bindingStorageType worldTyped.1 storage)).bind
    admitted (bound.bindingStorageType worldTyped).2

theorem FreshRegion.contextBindingsTyped {program : Kernel.Program} {before after : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before source runtime)
    {lexical region : Identity} (fresh : lexical ∉ source.static.scope.regions)
    (created : FreshRegion before region after) :
    Typing.ContextBindingsTyped program after (source.bindRegion lexical)
      { runtime.bindRegion lexical region with scope := region, region := region } := by
  have roots : after.roots = before.roots := by obtain ⟨_,_,rfl⟩ := created; rfl
  have loans : after.loans = before.loans := by obtain ⟨_,rfl⟩ := created; rfl
  exact (typed.world (fun _ _ located => located.roots_loans roots loans)).bindRegion fresh region

theorem FreshRegion.preserves_contextBindingsTyped {program : Kernel.Program} {before after : World}
    {source : Typing.Context} {runtime : Execution.Context} {region : Identity}
    (created : FreshRegion before region after) (typed : Typing.ContextBindingsTyped program before source runtime) :
    Typing.ContextBindingsTyped program after source runtime := by
  obtain ⟨_,rfl⟩ := created
  exact typed.world (fun _ _ binding => binding.roots_loans (before := before)
    (after := { before with liveRegions := region :: before.liveRegions, nextRegion := region+1 }) rfl rfl)

theorem Execution.Installs.preserves_contextBindingsTyped {program : Kernel.Program} {before : Execution.State}
    {outer : Execution.Context} {syntaxNode : Kernel.Handler} {handler : Execution.InstalledHandler} {after : World}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (installed : Execution.Installs program before outer syntaxNode handler after)
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before.world source runtime) :
    Typing.ContextBindingsTyped program after source runtime := by
  obtain ⟨_,_,_,_,_,_,_,_,one,two,_,captured,bound,retired,rfl,_⟩ := installed
  have secondWorld := two.worldTyped (one.worldTyped worldTyped)
  have secondContext := two.preserves_contextBindingsTyped (one.preserves_contextBindingsTyped typed)
  have capturedWorld := captured.worldTyped valid inventory secondWorld
  have capturedContext := captured.contextBindingsTyped valid inventory secondWorld secondContext
  exact (capturedContext.world (fun _ _ binding =>
    bound.preserves_bindingStorageType valid inventory capturedWorld binding)).world
      (fun _ _ binding => retired.bindingStorageTyped binding)

/-- Installation may move or borrow captures and retire the old temporary
owners. The computation retains the same lexical declarations, whose actual
availability is still checked by execution/resource admission. -/
theorem Execution.Installs.computation_contextBindingsTyped {program : Kernel.Program} {before : Execution.State}
    {outer : Execution.Context} {syntaxNode : Kernel.Handler} {handler : Execution.InstalledHandler} {after : World}
    {source : Typing.Context}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source outer)
    (installed : Execution.Installs program before outer syntaxNode handler after) :
    Typing.ContextBindingsTyped program after source handler.computation := by
  have retained := installed.preserves_contextBindingsTyped valid inventory worldTyped typed
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩ := installed
  exact ⟨retained.moduleEq,retained.unsafeEq,retained.covers,retained.distinct,retained.admitted,retained.bindings,retained.assumptions⟩

/-- The handler's retained environment is produced by the same sequential
input binding used at function entry. Source captures are closed exactly once
through the outer lexical map, and temporary retirement preserves their
declared storage types without asserting read availability. -/
theorem Execution.Installs.environment_contextBindingsTyped {program : Kernel.Program} {before : Execution.State}
    {outer : Execution.Context} {syntaxNode : Kernel.Handler} {handler : Execution.InstalledHandler} {after : World}
    {source : Typing.Context} {input result : Term}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source outer)
    (handlerTyped : Typing.HandlerType program source syntaxNode input result)
    (installed : Execution.Installs program before outer syntaxNode handler after) :
    Typing.ContextBindingsTyped program after
      { source with locals := Execution.CaptureLocals syntaxNode.captures } handler.environment := by
  obtain ⟨first,second,sources,captures,captured,bindings,bound,disposed,one,two,captureMap,capturedValues,boundValues,retired,rfl,rfl⟩ := installed
  have capturedWorld := capturedValues.worldTyped valid inventory (two.worldTyped (one.worldTyped worldTyped))
  have checked := boundValues.bindingStorageTypes valid inventory capturedWorld
  have aligned : (((Execution.CaptureLocals captures).zip sources).map (fun (localSlot,address) =>
      (⟨.capture 0,localSlot,address,.owner,.owned⟩ : Kernel.InvocationInput))).map (·.formal) =
      Execution.CaptureLocals captures := by
    simp only [List.map_map,Function.comp_def]
    exact List.map_fst_zip (by
      simpa only [Execution.CaptureLocals,List.length_map] using (Nat.le_of_eq capturedValues.length_eq))
  have declared : ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
      Typing.BindingStorageTyped program.declarations after binding.address localSlot.type)
      (Execution.CaptureLocals captures) bindings := by
    rw [← aligned]
    clear aligned boundValues
    generalize (((Execution.CaptureLocals captures).zip sources).map (fun (localSlot,address) =>
      (⟨.capture 0,localSlot,address,.owner,.owned⟩ : Kernel.InvocationInput))) = inputs at checked ⊢
    induction checked with
    | nil => exact .nil
    | cons head _ ih => exact .cons ⟨head.1,retired.bindingStorageTyped head.2⟩ ih
  have transport : ∀ (lexical : List Kernel.Capture) (environment : Kernel.Environment),
      ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
        Typing.BindingStorageTyped program.declarations after binding.address localSlot.type)
        (Execution.CaptureLocals (lexical.map (Kernel.Capture.mapTerms outer.term))) environment →
      ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
        Typing.BindingStorageTyped program.declarations after binding.address (outer.term localSlot.type))
        (Execution.CaptureLocals lexical) environment := by
    intro lexical
    induction lexical with
    | nil => intro environment related; cases related; exact .nil
    | cons capture rest ih =>
      intro environment related
      cases related with
      | cons head tail => exact .cons head (ih _ tail)
  have declared := transport syntaxNode.captures bindings (captureMap ▸ declared)
  refine ⟨typed.moduleEq,typed.unsafeEq,typed.covers,?_,?_,declared,typed.assumptions⟩
  · cases handlerTyped with
    | attached captureTyped _ _ _ =>
      simpa only [Execution.CaptureLocals,Kernel.Handler.captures,List.map_map,Function.comp_def] using captureTyped.2
  · intro localSlot member
    cases handlerTyped with
    | attached _ admitted _ _ =>
      obtain ⟨capture,present,rfl⟩ := List.mem_map.mp member
      exact admitted capture.type (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨capture,present,rfl⟩)))

theorem Execution.StartsClause.preserves_contextBindingsTyped {program : Kernel.Program} {before : Execution.State}
    {handler : Execution.InstalledHandler} {context : Execution.Context} {after : World}
    (started : Execution.StartsClause before handler context after)
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before.world source runtime) :
    Typing.ContextBindingsTyped program after source runtime :=
  started.1.preserves_contextBindingsTyped typed

/-- A handler clause gets a fresh cleanup activation but closes source names
through its retained handler environment. These are different identities. -/
theorem Execution.StartsClause.contextBindingsTyped {program : Kernel.Program} {before : Execution.State}
    {handler : Execution.InstalledHandler} {source : Typing.Context} {runtime : Execution.Context} {after : World}
    (typed : Typing.ContextBindingsTyped program before.world source handler.environment)
    (started : Execution.StartsClause before handler runtime after) :
    Typing.ContextBindingsTyped program after source runtime := by
  have retained := started.preserves_contextBindingsTyped typed
  obtain ⟨_,rfl⟩ := started
  exact ⟨retained.moduleEq,retained.unsafeEq,retained.covers,retained.distinct,retained.admitted,retained.bindings,retained.assumptions⟩

theorem Execution.StartsResumptionClause.preserves_contextBindingsTyped {program : Kernel.Program} {before : Execution.State}
    {handler : Execution.InstalledHandler} {lexical : Kernel.Local} {context : Execution.Context} {localSlot : Kernel.Local} {after : World}
    (started : Execution.StartsResumptionClause before handler lexical context localSlot after)
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before.world source runtime) :
    Typing.ContextBindingsTyped program after source runtime := by
  obtain ⟨_,_,started,_⟩ := started
  exact started.preserves_contextBindingsTyped typed

theorem Execution.StartsResumptionClause.contextBindingsTyped {program : Kernel.Program} {before : Execution.State}
    {handler : Execution.InstalledHandler} {source : Typing.Context} {runtime : Execution.Context} {after : World}
    {lexical localSlot : Kernel.Local}
    (typed : Typing.ContextBindingsTyped program before.world source handler.environment)
    (fresh : ∀ brand, lexical.resumptionBrand = some brand → brand ∉ source.static.scope.brands)
    (started : Execution.StartsResumptionClause before handler lexical runtime localSlot after) :
    Typing.ContextBindingsTyped program after (source.bindResumption (some lexical)) runtime := by
  obtain ⟨outer,brand,clause,selected,rfl,_⟩ := started
  have entered := clause.contextBindingsTyped typed
  simpa only [Typing.Context.bindResumption,Option.bind,selected] using
    entered.bindBrand (fresh brand selected) (.resumption before.nextContinuation)

theorem Typing.ContextBindingsTyped.label {program : Kernel.Program} {world : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program world source runtime)
    {lexical region : Identity} {result : Term}
    (fresh : lexical ∉ source.static.scope.brands) (brand : Identity) :
    Typing.ContextBindingsTyped program world
      { source.bindBrand lexical with labels := (lexical,.scopedRegion region,result) :: source.labels }
      (runtime.bindBrand lexical (.label brand)) := by
  have bound := typed.bindBrand fresh (.label brand)
  exact ⟨bound.moduleEq,bound.unsafeEq,bound.covers,bound.distinct,bound.admitted,bound.bindings,bound.assumptions⟩

/-- The label frame and its source-visible label value close through the same
lexical lookup. The surrounding allocation/cleanup region may be different,
as it is during a handler clause. -/
theorem Typing.ContextBindingsTyped.labelStep {program : Kernel.Program} {before : Execution.State}
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before.world source runtime)
    {lexical region : Identity} {result : Term} {body : Kernel.Code}
    (present : region ∈ source.static.scope.regions) (fresh : lexical ∉ source.static.scope.brands)
    (admitted : result.Scoped source.static.scope)
    (running : before.task = .run runtime (.label lexical region result body)) :
    ∃ selectedRegion,
      let inner := runtime.bindBrand lexical (.label before.nextBrand)
      Execution.LocalStep program before none
        { before with
          task := .run inner body
          frames := .label runtime before.nextBrand selectedRegion (runtime.term result) :: before.frames
          nextBrand := before.nextBrand+1 } ∧
      Typing.ContextBindingsTyped program before.world
        { source.bindBrand lexical with labels := (lexical,.scopedRegion region,result) :: source.labels } inner ∧
      inner.term (.label (.scopedBrand lexical) (.scopedRegion region) result) =
        .label (.runtimeBrand (.label before.nextBrand)) (.runtimeRegion selectedRegion) (runtime.term result) := by
  obtain ⟨selectedRegion,found⟩ := typed.covers.1 region present
  have unchanged := runtime.bindBrand_term (runtime := .label before.nextBrand) fresh admitted
  refine ⟨selectedRegion,?_,typed.label fresh before.nextBrand,?_⟩
  · rw [← unchanged]
    exact .label running found rfl
  · simp only [Execution.Context.term,Execution.Context.bindBrand,ScopeInstantiation.term,Table.get_set,
      found,Option.map,Option.getD] at unchanged ⊢
    rw [unchanged]

theorem Execution.EnterWorld.contextBindingsTyped {program : Kernel.Program} {before : Execution.State} {after : World}
    {caller runtime : Execution.Context} {function : Kernel.Function} {source : Execution.EntrySource}
    {id : DeclId} {arguments : List Term}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (selected : Kernel.Instance program id arguments function) (functionTyped : Typing.FunctionType program function)
    (formals : source.HasFormals function)
    (entered : Execution.EnterWorld program before caller function source runtime after) :
    Typing.ContextBindingsTyped program after (Typing.FunctionContext function runtime.module) runtime := by
  obtain ⟨withRegion,prepared,inputs,environment,declaration,_,fresh,prepares,bound,rfl,_⟩ := entered
  have aligned := prepares.formals formals
  have checked := bound.bindingStorageTypes valid inventory (prepares.worldTyped valid inventory (fresh.worldTyped worldTyped))
  have closed := selected.locals_scopeClosed valid inventory functionTyped
  refine ⟨rfl,rfl,function.entryScope_covers _ _,functionTyped.locals_nodup,?_,?_,functionTyped.assumptions_scoped _⟩
  · intro localSlot member
    exact (closed localSlot member).scoped _
  · change ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
      Typing.BindingStorageTyped program.declarations after binding.address
        ((function.entryScope before.world.nextRegion before.nextBrand).term localSlot.type))
      (function.captures ++ function.parameters) environment
    have inputClosed : ∀ input ∈ inputs, input.formal.type.ScopeClosed := by
      intro input member
      apply closed
      rw [← aligned]
      exact List.mem_map.mpr ⟨input,member,rfl⟩
    rw [← aligned]
    clear aligned prepares bound formals closed
    induction checked with
    | nil => exact .nil
    | cons first _ ih =>
      refine .cons ⟨first.1,?_⟩ (ih (fun input member => inputClosed input (List.mem_cons_of_mem _ member)))
      rw [ScopeInstantiation.term_fixed _ _ (inputClosed _ List.mem_cons_self)]
      exact first.2

end Glorious.Language
