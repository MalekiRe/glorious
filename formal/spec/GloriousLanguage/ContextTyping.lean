import GloriousLanguage.InputTyping
import GloriousLanguage.LocalPreservation

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

/-- Only formal selection is required here. Access, initialization and
storage are checked by the existing recipe and binding producers. -/
def EntrySource.HasFormals (function : Kernel.Function) : EntrySource → Prop
  | .supplied inputs => inputs.map (·.formal) = function.captures ++ function.parameters
  | .resident _ _ arguments => arguments.map (·.formal) = function.parameters
  | .contextual _ _ _ _ inputs => inputs.map (·.formal) = function.captures ++ function.parameters

theorem ArgumentInputs.formals {world : World} {context : Context} {index : Nat}
    {formals : List Kernel.Local} {places : List Kernel.Place} {inputs : List Kernel.InvocationInput}
    (selected : ArgumentInputs world context index formals places inputs) : inputs.map (·.formal) = formals := by
  induction selected with
  | nil => rfl
  | cons _ _ _ ih => simp only [List.map_cons,ih]

theorem CaptureInputs.formals {world : World} {receiver : Address} {authority : Authority} {access : Access}
    {formals : List Kernel.Local} {inputs : List Kernel.InvocationInput}
    (selected : CaptureInputs world receiver authority access formals inputs) : inputs.map (·.formal) = formals := by
  rw [selected.1]
  simp only [List.map_map,Function.comp_def,List.zipIdx_map_fst]

theorem PreparesEntry.formals {program : Kernel.Program} {context : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List Kernel.InvocationInput}
    (prepared : PreparesEntry program context function before source inputs after)
    (formals : source.HasFormals function) : inputs.map (·.formal) = function.captures ++ function.parameters := by
  cases prepared with
  | supplied => exact formals
  | resident _ captures =>
    simpa only [List.map_append,captures.formals,EntrySource.HasFormals] using congrArg (function.captures ++ ·) formals
  | contextual => exact formals

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

/-- Scoped local storage typing only. This does not assert initialization,
loan permission, active labels or that arbitrary execution can make progress. -/
structure ContextBindingsTyped (program : Kernel.Program) (world : World)
    (source : Context) (runtime : Execution.Context) : Prop where
  moduleEq : runtime.module = source.static.module
  unsafeEq : runtime.unsafeAllowed = source.static.unsafeAllowed
  covers : runtime.instantiation.Covers source.static.scope
  distinct : (source.locals.map (·.id)).Nodup
  admitted : ∀ localSlot ∈ source.locals, localSlot.type.Scoped source.static.scope
  bindings : ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
    AddressType program.declarations world binding.address (runtime.term localSlot.type)) source.locals runtime.environment

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
      AddressType program.declarations world binding.address (runtime.term localSlot.type) := by
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

theorem Typing.ContextBindingsTyped.world {program : Kernel.Program} {before after : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before source runtime)
    (preserved : ∀ address type, AddressType program.declarations before address type →
      AddressType program.declarations after address type) :
    Typing.ContextBindingsTyped program after source runtime := by
  exact ⟨typed.moduleEq,typed.unsafeEq,typed.covers,typed.distinct,typed.admitted,
    typed.bindings.imp (fun _ _ pair => ⟨pair.1,preserved _ _ pair.2⟩)⟩

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
    (located : AddressType program.declarations world address (runtime.term localSlot.type)) :
    Typing.ContextBindingsTyped program world (source.bind localSlot)
      (runtime.bind (runtime.local localSlot) address authority) := by
  refine ⟨typed.moduleEq,typed.unsafeEq,typed.covers,?_,?_,?_⟩
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
  refine ⟨typed.moduleEq,typed.unsafeEq,typed.covers.bindBrand lexical brand,typed.distinct,?_,?_⟩
  · intro localSlot member
    exact (typed.admitted localSlot member).mono (fun _ member => member)
      (fun _ member => List.mem_cons_of_mem _ member)
  · have related := typed.bindings
    have admitted := typed.admitted
    change ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
      AddressType program.declarations world binding.address ((runtime.bindBrand lexical brand).term localSlot.type))
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
  refine ⟨typed.moduleEq,typed.unsafeEq,typed.covers.bindRegion lexical region,typed.distinct,?_,?_⟩
  · intro localSlot member
    exact (typed.admitted localSlot member).mono (fun _ member => List.mem_cons_of_mem _ member)
      (fun _ member => member)
  · have related := typed.bindings
    have admitted := typed.admitted
    change ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
      AddressType program.declarations world binding.address ((runtime.bindRegion lexical region).term localSlot.type))
      source.locals runtime.environment
    generalize source.locals = locals at related admitted ⊢
    generalize runtime.environment = environment at related ⊢
    induction related with
    | nil => exact .nil
    | @cons localSlot binding locals bindings first rest ih =>
      refine ListRel.cons ⟨first.1,?_⟩ ?_
      · change AddressType program.declarations world binding.address ((runtime.bindRegion lexical region).term localSlot.type)
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
  exact (typed.world (fun _ _ located => allocated.addressType world located)).bind admitted allocated.created_addressType

theorem FreshRegion.contextBindingsTyped {program : Kernel.Program} {before after : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (typed : Typing.ContextBindingsTyped program before source runtime)
    {lexical region : Identity} (fresh : lexical ∉ source.static.scope.regions)
    (created : FreshRegion before region after) :
    Typing.ContextBindingsTyped program after (source.bindRegion lexical)
      { runtime.bindRegion lexical region with scope := region, region := region } := by
  have roots : after.roots = before.roots := by obtain ⟨_,_,rfl⟩ := created; rfl
  exact (typed.world (fun _ _ located => located.roots_congr roots)).bindRegion fresh region

/-- A handler clause gets a fresh cleanup activation but closes source names
through its retained handler environment. These are different identities. -/
theorem Execution.StartsClause.contextBindingsTyped {program : Kernel.Program} {before : Execution.State}
    {handler : Execution.InstalledHandler} {source : Typing.Context} {runtime : Execution.Context} {after : World}
    (typed : Typing.ContextBindingsTyped program before.world source handler.environment)
    (started : Execution.StartsClause before handler runtime after) :
    Typing.ContextBindingsTyped program after source runtime := by
  obtain ⟨created,rfl⟩ := started
  have roots : after.roots = before.world.roots := by obtain ⟨_,_,rfl⟩ := created; rfl
  have retained := typed.world (fun _ _ located => located.roots_congr roots)
  exact ⟨retained.moduleEq,retained.unsafeEq,retained.covers,retained.distinct,retained.admitted,retained.bindings⟩

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
  exact ⟨bound.moduleEq,bound.unsafeEq,bound.covers,bound.distinct,bound.admitted,bound.bindings⟩

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
  have checked := bound.inputTypes valid inventory (prepares.worldTyped valid inventory (fresh.worldTyped worldTyped))
  have closed := selected.locals_scopeClosed valid inventory functionTyped
  refine ⟨rfl,rfl,function.entryScope_covers _ _,functionTyped.locals_nodup,?_,?_⟩
  · intro localSlot member
    exact (closed localSlot member).scoped _
  · change ListRel (fun localSlot binding => binding.localSlot = localSlot.id ∧
      AddressType program.declarations after binding.address
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
      exact first.2.2

end Glorious.Language
