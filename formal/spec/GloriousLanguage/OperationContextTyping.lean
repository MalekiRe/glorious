import GloriousLanguage.PatternContextTyping
import GloriousLanguage.EffectContextTyping

/-! Source operation-arm typing is consumed by the actual selected clause.
Continuation binding precedes the payload's ordered pattern binders, exactly
as in the executable suspension transition. -/
namespace Glorious.Language

theorem Typing.CallSignature.parameters_scoped {program : Program} (valid : ProgramWellFormed program)
    {context : Language.Context} {id : DeclId} {arguments : List Term} {signature : Signature}
    (selected : Typing.CallSignature program context id arguments signature) :
    ∀ type ∈ signature.parameters, type.Scoped context.scope := by
  obtain ⟨kinded,selected⟩ := selected
  rcases selected with selected | selected
  all_goals obtain ⟨declaration,substitution,found,instantiated,_,rfl⟩ := selected
  all_goals intro type member
  all_goals obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  all_goals
    refine Term.Scoped.substitute substitution original ?_
      (fun _ value found => (kinded value (instantiated.argument_of_get found)).scoped)
  · apply Term.ScopeClosed.scoped
    apply valid.scopeClosed (List.mem_of_find?_eq_some (Program.function_lookup found))
    simp only [Definition.terms,Signature.terms,List.mem_append,List.mem_cons]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr present)))))
  · apply Term.ScopeClosed.scoped
    apply valid.scopeClosed (List.mem_of_find?_eq_some (Program.operation_lookup found))
    simp only [Definition.terms,Signature.terms,List.mem_append,List.mem_cons]
    exact Or.inl (Or.inl (Or.inr (Or.inr present)))

theorem Typing.PatternsType.locals_scoped {program : Program} (valid : ProgramWellFormed program)
    {context : Language.Context} {patterns : List Kernel.Pattern} {types : List Term} {access : Access}
    {locals : List Kernel.Local} (typed : Typing.PatternsType program context patterns types access locals)
    (admitted : ∀ type ∈ types, type.Scoped context.scope) :
    ∀ localSlot ∈ locals, localSlot.type.Scoped context.scope := by
  induction patterns generalizing types locals with
  | nil => cases typed; simp
  | cons pattern patterns ih =>
    cases typed with
    | cons first rest =>
      intro localSlot member
      rcases List.mem_append.mp member with firstMember | laterMember
      · exact first.locals_scoped valid (admitted _ List.mem_cons_self) localSlot firstMember
      · exact ih rest (fun type member => admitted type (List.mem_cons_of_mem _ member)) localSlot laterMember

/-- Selection projects the existing operation typing derivation; it does not
recheck an arm or infer a second list of payload binders. -/
theorem Typing.OperationArmsType.member {program : Kernel.Program} {context : Typing.Context}
    {arms : List Kernel.OperationArm} {result : Term}
    (typed : Typing.OperationArmsType program context arms result) {arm : Kernel.OperationArm} (member : arm ∈ arms) :
    ∃ signature locals output,
      Typing.CallSignature program.declarations context.static arm.operation arm.arguments signature ∧
      Typing.PatternsType program.declarations context.static arm.patterns signature.parameters .owned locals ∧
      (∀ brand, arm.continuation.bind Kernel.Local.resumptionBrand = some brand → brand ∉ context.static.scope.brands) ∧
      Typing.TermsScoped (context.bindResumption arm.continuation) (output :: arm.continuation.toList.map (·.type)) ∧
      Typing.CodeType program ((context.bindResumption arm.continuation).bindLocals (arm.continuation.toList ++ locals)) arm.body output := by
  induction arms with
  | nil => cases member
  | cons first rest ih =>
    cases typed with
    | cons _ signature patterns _ fresh admitted body tail =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_,_,_,signature,patterns,fresh,admitted,body⟩
      · exact ih tail member

theorem Typing.Context.scoped_bindResumption {context : Typing.Context} {term : Term}
    (admitted : term.Scoped context.static.scope) (continuation : Option Kernel.Local) :
    term.Scoped (context.bindResumption continuation).static.scope := by
  unfold Typing.Context.bindResumption
  split
  · exact admitted
  · exact admitted.mono (fun _ member => member) (fun _ member => List.mem_cons_of_mem _ member)

namespace Execution

theorem SelectsOperation.member {program : Kernel.Program} {world : World} {handler : InstalledHandler}
    {operation : DeclId} {arguments : List Term} {payload : List ResolvedPlace} {arm : Kernel.OperationArm}
    (selected : SelectsOperation program world handler operation arguments payload arm) : arm ∈ handler.syntaxNode.operations := by
  obtain ⟨skipped,rest,arms,_⟩ := selected
  rw [arms]
  exact List.mem_append_right _ List.mem_cons_self

theorem Routes.handler_member {program : Kernel.Program} {before : State} {operation : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace} {inner outer : List Frame}
    {handler : InstalledHandler} {owns : Bool} {arm : Kernel.OperationArm}
    (routed : Routes program before operation arguments payload inner handler owns arm outer) :
    Frame.handler handler owns ∈ before.frames := by
  rw [routed.1]
  exact List.mem_append_right _ List.mem_cons_self

theorem PayloadPlan.nonBinding_segments {program : Program} {world : World} {addresses : List Address}
    {patterns : List Kernel.Pattern} {actions : Kernel.PatternActions}
    (planned : PayloadPlan program world addresses patterns actions) :
    actions.shells.filterMap Kernel.PatternAction.boundLocal = [] ∧
      actions.cleanup.filterMap Kernel.PatternAction.boundLocal = [] := by
  induction planned with
  | nil => exact ⟨rfl,rfl⟩
  | cons first _ ih =>
    have firstEmpty := first.nonBinding_segments
    simp only [List.filterMap_append,firstEmpty.1,firstEmpty.2,ih.1,ih.2,List.nil_append,and_self]

theorem _root_.Glorious.Language.Typing.PatternsType.payload_bindingLocals {program : Program}
    {context : Language.Context} {patterns : List Kernel.Pattern} {types : List Term} {access : Access}
    {locals : List Kernel.Local} (typed : Typing.PatternsType program context patterns types access locals)
    (close : Term → Term) {world : World} {addresses : List Address} {actions : Kernel.PatternActions}
    (planned : PayloadPlan program world addresses (patterns.map (Kernel.Pattern.mapTerms close)) actions) :
    actions.bindings.filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms close) := by
  induction patterns generalizing types locals addresses actions with
  | nil => cases typed; cases planned; rfl
  | cons pattern patterns ih =>
    cases typed with
    | cons first rest =>
      cases planned with
      | cons firstPlan restPlan =>
        simp only [List.filterMap_append,List.map_append,first.plan_bindingLocals close firstPlan,ih rest restPlan]

theorem _root_.Glorious.Language.Typing.PatternsType.payload_scheduled_bindingLocals {program : Program}
    {context : Language.Context} {patterns : List Kernel.Pattern} {types : List Term} {access : Access}
    {locals : List Kernel.Local} (typed : Typing.PatternsType program context patterns types access locals)
    (close : Term → Term) {world : World} {addresses : List Address} {actions : Kernel.PatternActions}
    (planned : PayloadPlan program world addresses (patterns.map (Kernel.Pattern.mapTerms close)) actions) :
    (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms close) := by
  have empty := planned.nonBinding_segments
  simp only [ScheduledPattern,List.filterMap_append,empty.1,empty.2,List.nil_append,List.append_nil,
    typed.payload_bindingLocals close planned]

/-- The actual installed frame provides the source operation typing and the
newly bound capture environment consumed later by dispatch. -/
theorem Installs.operationArms_context {program : Kernel.Program} {before : State}
    {outer : Context} {syntaxNode : Kernel.Handler} {handler : InstalledHandler} {after : World}
    {source : Typing.Context} {input result : Term}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source outer)
    (handlerTyped : Typing.HandlerType program source syntaxNode input result)
    (installed : Installs program before outer syntaxNode handler after) :
    ∃ environment,
      Typing.ContextBindingsTyped program after environment handler.environment ∧
      Typing.OperationArmsType program environment handler.syntaxNode.operations result := by
  have environment := installed.environment_contextBindingsTyped valid inventory worldTyped typed handlerTyped
  refine ⟨{ source with locals := CaptureLocals syntaxNode.captures },environment,?_⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩ := installed
  cases handlerTyped with
  | attached _ _ _ operations => exact operations

theorem CreatesContinuation.contextBindingsTyped {program : Kernel.Program} {context : Context} {before after : World}
    {id signature answer effects quantity address} {lexical : Kernel.Local} {source : Typing.Context}
    (worldTyped : Typing.WorldTyped program before)
    (typed : Typing.ContextBindingsTyped program before source context)
    (admitted : lexical.type.Scoped source.static.scope)
    (created : CreatesContinuation program context before id signature answer effects quantity (context.local lexical) address after) :
    Typing.ContextBindingsTyped program after (source.bind lexical) (context.bind (context.local lexical) address) := by
  have retained := created.preserves_contextBindingsTyped worldTyped typed
  obtain ⟨_,_,_,allocated,constructed⟩ := created
  exact retained.bind admitted (constructed.bindingStorageTyped (allocated.wellFormed worldTyped.1)
    allocated.created_bindingStorageTyped)

/-- The ordinary suspension clause binds its continuation first, then leaves
the source payload binders to the actual scheduled pattern actions. -/
theorem suspend_inputs_context {program : Kernel.Program} {before : State} {source : Typing.Context}
    {handler : InstalledHandler} {result : Term} {operation : DeclId} {arguments : List Term}
    {payload : List ResolvedPlace} {arm : Kernel.OperationArm} {lexical localSlot : Kernel.Local}
    {clause : Context} {withRegion moved created : World} {kept : List Address} {roots : List Identity}
    {signature : Signature} {answer effects : Term} {quantity : Quantity} {address : Address} {actions : Kernel.PatternActions}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source handler.environment)
    (armsTyped : Typing.OperationArmsType program source handler.syntaxNode.operations result)
    (selected : SelectsOperation program before.world handler operation arguments payload arm)
    (continuation : arm.continuation = some lexical)
    (started : StartsResumptionClause before handler lexical clause localSlot withRegion)
    (keptValues : Protects program clause withRegion payload kept moved)
    (constructed : CreatesContinuation program clause (suspendRoots moved roots before.nextContinuation) before.nextContinuation
      signature answer effects quantity localSlot address created)
    (planned : PayloadPlan program.declarations created kept (arm.patterns.map (Kernel.Pattern.mapTerms clause.term)) actions) :
    ∃ locals output,
      Typing.ContextBindingsTyped program created ((source.bindResumption (some lexical)).bind lexical) (clause.bind localSlot address) ∧
      Typing.CodeType program (((source.bindResumption (some lexical)).bind lexical).bindLocals locals) arm.body output ∧
      (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms clause.term) ∧
      ∀ localSlot ∈ locals, localSlot.type.Scoped (source.bindResumption (some lexical)).static.scope := by
  obtain ⟨selectedSignature,locals,output,signatureTyped,patternsTyped,fresh,admitted,bodyTyped⟩ := armsTyped.member selected.member
  rw [continuation] at fresh admitted bodyTyped
  have startedContext := started.contextBindingsTyped typed (fun brand found => fresh brand found)
  have withRegionTyped := started.worldTyped worldTyped
  have movedTyped := keptValues.worldTyped valid inventory withRegionTyped
  have movedContext := keptValues.contextBindingsTyped valid inventory withRegionTyped startedContext
  have suspendedTyped := suspendRoots.worldTyped movedTyped (roots := roots) (id := before.nextContinuation)
  have suspendedContext := suspendRoots.contextBindingsTyped movedContext (roots := roots) (id := before.nextContinuation)
  have localEq : localSlot = clause.local lexical := by obtain ⟨_,_,_,_,_,localEq⟩ := started; exact localEq
  have localScoped : lexical.type.Scoped (source.bindResumption (some lexical)).static.scope :=
    admitted _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have createdContext := (localEq ▸ constructed).contextBindingsTyped suspendedTyped suspendedContext localScoped
  refine ⟨locals,output,by simpa only [localEq] using createdContext,bodyTyped,
    patternsTyped.payload_scheduled_bindingLocals clause.term planned,?_⟩
  intro localSlot member
  exact Typing.Context.scoped_bindResumption
    (patternsTyped.locals_scoped valid (signatureTyped.parameters_scoped valid) localSlot member) _

theorem suspend_tail_inputs_context {program : Kernel.Program} {before : State} {source : Typing.Context}
    {handler : InstalledHandler} {result : Term} {operation : DeclId} {arguments : List Term}
    {payload : List ResolvedPlace} {arm : Kernel.OperationArm} {clause : Context} {withRegion moved : World}
    {kept : List Address} {roots : List Identity} {actions : Kernel.PatternActions}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source handler.environment)
    (armsTyped : Typing.OperationArmsType program source handler.syntaxNode.operations result)
    (selected : SelectsOperation program before.world handler operation arguments payload arm)
    (continuation : arm.continuation = none)
    (started : StartsClause before handler clause withRegion)
    (keptValues : Protects program clause withRegion payload kept moved)
    (planned : PayloadPlan program.declarations moved kept (arm.patterns.map (Kernel.Pattern.mapTerms clause.term)) actions) :
    ∃ locals output,
      Typing.ContextBindingsTyped program (suspendRoots moved roots before.nextContinuation) source clause ∧
      Typing.CodeType program (source.bindLocals locals) arm.body output ∧
      (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms clause.term) ∧
      ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope := by
  obtain ⟨signature,locals,output,signatureTyped,patternsTyped,_,_,bodyTyped⟩ := armsTyped.member selected.member
  have entered := started.contextBindingsTyped typed
  have movedContext := keptValues.contextBindingsTyped valid inventory (started.worldTyped worldTyped) entered
  refine ⟨locals,output,suspendRoots.contextBindingsTyped movedContext,?_,
    patternsTyped.payload_scheduled_bindingLocals clause.term planned,
    patternsTyped.locals_scoped valid (signatureTyped.parameters_scoped valid)⟩
  simpa only [continuation,Typing.Context.bindResumption,Option.bind,Option.toList,List.nil_append] using bodyTyped

/-- Every actual suspension dispatch starts a source-typed pattern body.
The frame premise describes only existing input handlers; installation above
derives it from their source HandlerType and real capture bindings. -/
theorem EffectStep.suspended_clause_context {program : Kernel.Program} {before after : State} {id : Identity}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (handlers : ∀ handler owns, Frame.handler handler owns ∈ before.frames →
      ∃ source result, Typing.ContextBindingsTyped program before.world source handler.environment ∧
        Typing.OperationArmsType program source handler.syntaxNode.operations result)
    (step : EffectStep program before (some (.suspend id)) after) :
    ∃ source runtime actions body locals result,
      after.task = .pattern runtime (ScheduledPattern actions) body ∧
      Typing.ContextBindingsTyped program after.world source runtime ∧
      Typing.CodeType program (source.bindLocals locals) body result ∧
      (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms runtime.term) ∧
      ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope := by
  cases step with
  | suspend _ _ _ _ _ continuation routed started keptValues _ _ _ constructed planned _ =>
    obtain ⟨source,result,contextTyped,armsTyped⟩ := handlers _ _ routed.handler_member
    obtain ⟨locals,output,context,body,binders,admitted⟩ := suspend_inputs_context valid inventory worldTyped contextTyped armsTyped
      routed.2.2 continuation started keptValues constructed planned
    exact ⟨_,_,_,_,locals,output,rfl,context,body,binders,admitted⟩
  | suspendTailArm _ _ _ _ _ _ continuation routed started keptValues _ _ _ planned _ =>
    obtain ⟨source,result,contextTyped,armsTyped⟩ := handlers _ _ routed.handler_member
    obtain ⟨locals,output,context,body,binders,admitted⟩ := suspend_tail_inputs_context valid inventory worldTyped contextTyped armsTyped
      routed.2.2 continuation started keptValues planned
    exact ⟨_,_,_,_,locals,output,rfl,context,body,binders,admitted⟩

end Execution
end Glorious.Language
