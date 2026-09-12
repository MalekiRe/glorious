import GloriousLanguage.PatternExecutionTyping

/-! Terminal and completion dispatch consume the selected source clause and
its actual pattern plan. Their cleanup remains explicit in the resulting
task: typing at dispatch is not permission to discard a retained lease. -/
namespace Glorious.Language

theorem Typing.ArmsType.member {program : Kernel.Program} {context : Typing.Context}
    {arms : List Kernel.Arm} {input result : Term}
    (typed : Typing.ArmsType program context arms input result)
    {arm : Kernel.Arm} (member : arm ∈ arms) :
    ∃ locals, Typing.PatternType program.declarations context.static arm.pattern input .owned locals ∧
      Typing.CodeType program (context.bindLocals locals) arm.body result := by
  induction arms with
  | nil => cases member
  | cons first rest ih =>
    cases typed with
    | cons pattern _ body tail =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_,pattern,body⟩
      · exact ih tail member

/-- A terminal declaration's selected arm returns the handler result, not
the operation's bottom result or a tail-resumption result. -/
theorem Typing.OperationArmsType.terminal_member {program : Kernel.Program} {context : Typing.Context}
    {arms : List Kernel.OperationArm} {result : Term}
    (typed : Typing.OperationArmsType program context arms result)
    {arm : Kernel.OperationArm} (member : arm ∈ arms) {operation : OperationDefinition}
    (selected : program.declarations.operation arm.operation = some operation)
    (terminal : operation.terminal = true) :
    ∃ signature locals,
      Typing.CallSignature program.declarations context.static arm.operation arm.arguments signature ∧
      Typing.PatternsType program.declarations context.static arm.patterns signature.parameters .owned locals ∧
      Typing.CodeType program (context.bindLocals locals) arm.body result := by
  induction arms with
  | nil => cases member
  | cons first rest ih =>
    cases typed with
    | cons found signature patterns kind _ _ body tail =>
      rcases List.mem_cons.mp member with rfl | member
      · have same := Option.some.inj (found.symm.trans selected)
        subst operation
        rcases kind with ⟨_,continuation,output⟩ | ⟨notTerminal,_⟩
        · refine ⟨_,_,signature,patterns,?_⟩
          simpa only [continuation,output,Typing.Context.bindResumption,Option.bind,
            Option.toList,List.nil_append,Kernel.OperationArm.body] using body
        · simp_all
      · exact ih tail member

namespace Kernel

theorem FirstArm.member {program : Language.Program} {world : World} {address : Address}
    {arms : List Arm} {arm : Arm} (selected : FirstArm program world address arms arm) : arm ∈ arms := by
  obtain ⟨skipped,rest,arms,_⟩ := selected
  rw [arms]
  exact List.mem_append_right _ List.mem_cons_self

end Kernel

theorem Typing.CompletionType.selected {program : Kernel.Program} {context : Typing.Context}
    {arms : List Kernel.Arm} {input result : Term}
    (typed : Typing.CompletionType program context arms input result)
    {world : World} {address : Address} {arm : Kernel.Arm}
    (selected : Kernel.FirstArm program.declarations world address arms arm) :
    ∃ locals, Typing.PatternType program.declarations context.static arm.pattern input .owned locals ∧
      Typing.CodeType program (context.bindLocals locals) arm.body result := by
  cases typed with
  | identity => cases selected.member
  | arms _ _ armsTyped => exact armsTyped.member selected.member

theorem Typing.CompletionType.empty {program : Kernel.Program} {context : Typing.Context}
    {arms : List Kernel.Arm} {input result : Term}
    (typed : Typing.CompletionType program context arms input result) (empty : arms = []) :
    Equal program.declarations context.static input result := by
  cases typed with
  | identity equal => exact equal
  | arms nonempty _ _ => exact False.elim (nonempty empty)

namespace Execution

theorem SelectsOperation.operation {program : Kernel.Program} {world : World} {handler : InstalledHandler}
    {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace} {arm : Kernel.OperationArm}
    (selected : SelectsOperation program world handler id arguments payload arm) : arm.operation = id := by
  obtain ⟨_,_,_,accepts,_⟩ := selected
  have identity := accepts.1
  cases arm
  exact identity

/-- Installation produces the completion-clause environment and its source
input scope from HandlerType, through the real capture bindings. -/
theorem Installs.completion_context {program : Kernel.Program} {before : State}
    {outer : Context} {syntaxNode : Kernel.Handler} {handler : InstalledHandler} {after : World}
    {source : Typing.Context} {input result : Term}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source outer)
    (handlerTyped : Typing.HandlerType program source syntaxNode input result)
    (installed : Installs program before outer syntaxNode handler after) :
    ∃ environment,
      Typing.ContextBindingsTyped program after environment handler.environment ∧
      input.Scoped environment.static.scope ∧
      Typing.CompletionType program environment handler.syntaxNode.completion input result := by
  have environment := installed.environment_contextBindingsTyped valid inventory worldTyped typed handlerTyped
  refine ⟨{ source with locals := CaptureLocals syntaxNode.captures },environment,?_⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩ := installed
  cases handlerTyped with
  | attached _ admitted completion _ => exact ⟨admitted _ List.mem_cons_self,completion⟩

/-- The source terminal result and payload binder order are transported by
the actual clause start and payload protection, before destructive cleanup. -/
theorem terminal_inputs_context {program : Kernel.Program} {before : State} {source : Typing.Context}
    {handler : InstalledHandler} {result : Term} {id : DeclId} {arguments : List Term}
    {payload : List ResolvedPlace} {arm : Kernel.OperationArm} {operation : OperationDefinition}
    {signature : Signature} {clause : Context} {withRegion moved : World}
    {kept : List Address} {actions : Kernel.PatternActions}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source handler.environment)
    (armsTyped : Typing.OperationArmsType program source handler.syntaxNode.operations result)
    (selected : SelectsOperation program before.world handler id arguments payload arm)
    (instanceTyped : OperationInstance program id arguments operation signature)
    (terminal : operation.terminal = true)
    (started : StartsClause before handler clause withRegion)
    (keptValues : Protects program clause withRegion payload kept moved)
    (planned : PayloadPlan program.declarations moved kept (arm.patterns.map (Kernel.Pattern.mapTerms clause.term)) actions) :
    ∃ locals,
      Typing.ContextBindingsTyped program moved source clause ∧
      Typing.CodeType program (source.bindLocals locals) arm.body result ∧
      (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms clause.term) ∧
      ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope := by
  obtain ⟨_,found,_⟩ := instanceTyped
  rw [← selected.operation] at found
  obtain ⟨_,locals,signatureTyped,patternsTyped,bodyTyped⟩ :=
    armsTyped.terminal_member selected.member found terminal
  have entered := started.contextBindingsTyped typed
  have movedContext := keptValues.contextBindingsTyped valid inventory (started.worldTyped worldTyped) entered
  exact ⟨locals,movedContext,bodyTyped,patternsTyped.payload_scheduled_bindingLocals clause.term planned,
    patternsTyped.locals_scoped valid (signatureTyped.parameters_scoped valid)⟩

theorem completion_inputs_context {program : Kernel.Program} {before : State} {source : Typing.Context}
    {handler : InstalledHandler} {input result : Term} {value kept : Address}
    {arm : Kernel.Arm} {clause : Context} {withRegion moved : World} {actions : Kernel.PatternActions}
    (valid : ProgramWellFormed program.declarations)
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source handler.environment)
    (admitted : input.Scoped source.static.scope)
    (completionTyped : Typing.CompletionType program source handler.syntaxNode.completion input result)
    (started : StartsClause before handler clause withRegion)
    (keptValue : Protect program clause withRegion value .owner kept moved)
    (selected : Kernel.FirstArm program.declarations moved kept handler.syntaxNode.completion arm)
    (planned : Kernel.PatternPlan program.declarations moved kept .owner .owned (arm.pattern.mapTerms clause.term) actions) :
    ∃ locals,
      Typing.ContextBindingsTyped program moved source clause ∧
      Typing.CodeType program (source.bindLocals locals) arm.body result ∧
      (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms clause.term) ∧
      ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope := by
  obtain ⟨locals,patternTyped,bodyTyped⟩ := completionTyped.selected selected
  have entered := started.contextBindingsTyped typed
  have movedContext := keptValue.contextBindingsTyped (started.worldTyped worldTyped) entered
  exact ⟨locals,movedContext,bodyTyped,patternTyped.scheduled_bindingLocals clause.term planned,
    patternTyped.locals_scoped valid admitted⟩

/-- Terminal transfer retains its selected handler and actual delimiter
cleanup. The scheduled body has the handler's source result type. -/
theorem EffectStep.terminal_clause_context {program : Kernel.Program} {before after : State}
    {context : Context} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (handlers : ∀ handler owns, Frame.handler handler owns ∈ before.frames →
      ∃ source result, Typing.ContextBindingsTyped program before.world source handler.environment ∧
        Typing.OperationArmsType program source handler.syntaxNode.operations result)
    (running : before.task = .perform context id arguments payload)
    (step : EffectStep program before none after) :
    ∃ source clause inner handler owns outer roots actions, ∃ arm : Kernel.OperationArm, ∃ result locals,
      before.frames = inner ++ Frame.handler handler owns :: outer ∧
      after.frames = Frame.serviced handler owns clause none :: outer ∧
      after.task = .cleanup context roots
        (CloseRegions (inner.flatMap Frame.ownedRegions ++ [handler.computation.region])
          (.pattern clause (ScheduledPattern actions) arm.body)) ∧
      Typing.ContextBindingsTyped program after.world source clause ∧
      Typing.CodeType program (source.bindLocals locals) arm.body result ∧
      (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms clause.term) ∧
      ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope := by
  cases step <;> try (solve | simp_all)
  case terminal running' instanceTyped terminal _ routed started keptValues _ _ planned =>
    rcases Task.perform.inj (running'.symm.trans running) with ⟨rfl,rfl,rfl,rfl⟩
    obtain ⟨source,result,contextTyped,armsTyped⟩ := handlers _ _ routed.handler_member
    obtain ⟨locals,contextTyped,bodyTyped,binders,admitted⟩ :=
      terminal_inputs_context valid inventory worldTyped contextTyped armsTyped routed.2.2
        instanceTyped terminal started keptValues planned
    exact ⟨source,_,_,_,_,_,_,_,_,result,locals,routed.1,rfl,rfl,contextTyped,bodyTyped,binders,admitted⟩

/-- Completion preserves identity completion as a distinct source contract;
an explicit arm carries its own actual ordered binder product. Both remain
behind the computation's scheduled scope cleanup. -/
theorem EffectStep.completion_context {program : Kernel.Program} {before after : State} {event : Option Event}
    {context : Context} {value : Address} {handler : InstalledHandler} {owns : Bool} {rest : List Frame}
    {source : Typing.Context} {input result : Term}
    (valid : ProgramWellFormed program.declarations)
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source handler.environment)
    (admitted : input.Scoped source.static.scope)
    (completionTyped : Typing.CompletionType program source handler.syntaxNode.completion input result)
    (running : before.task = .yield context value)
    (frames : before.frames = Frame.handler handler owns :: rest)
    (step : EffectStep program before event after) :
    event = none ∧ ∃ clause roots,
      Typing.ContextBindingsTyped program after.world source clause ∧
      after.frames = Frame.completion handler owns clause :: rest ∧
      ((∃ kept, after.task = .cleanup context roots
          (.closeRegion handler.computation.region (.yield clause kept)) ∧
          Equal program.declarations source.static input result) ∨
        ∃ arm : Kernel.Arm, ∃ actions locals,
          after.task = .cleanup context roots
            (.closeRegion handler.computation.region (.pattern clause (ScheduledPattern actions) arm.body)) ∧
          Typing.CodeType program (source.bindLocals locals) arm.body result ∧
          (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms clause.term) ∧
          ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope) := by
  cases step <;> try (solve | simp_all)
  case completionIdentity running' frames' empty started keptValue _ _ =>
    rcases Task.yield.inj (running'.symm.trans running) with ⟨rfl,rfl⟩
    rcases List.cons.inj (frames'.symm.trans frames) with ⟨same,rfl⟩
    rcases Frame.handler.inj same with ⟨rfl,rfl⟩
    have entered := started.contextBindingsTyped typed
    have movedContext := keptValue.contextBindingsTyped (started.worldTyped worldTyped) entered
    exact ⟨rfl,_,_,movedContext,rfl,Or.inl ⟨_,rfl,completionTyped.empty empty⟩⟩
  case completion running' frames' started keptValue _ _ selected planned =>
    rcases Task.yield.inj (running'.symm.trans running) with ⟨rfl,rfl⟩
    rcases List.cons.inj (frames'.symm.trans frames) with ⟨same,rfl⟩
    rcases Frame.handler.inj same with ⟨rfl,rfl⟩
    obtain ⟨locals,contextTyped,bodyTyped,binders,localsScoped⟩ :=
      completion_inputs_context valid worldTyped typed admitted completionTyped started keptValue selected planned
    exact ⟨rfl,_,_,contextTyped,rfl,Or.inr ⟨_,_,locals,rfl,bodyTyped,binders,localsScoped⟩⟩

theorem Step.performing_effect {program : Kernel.Program} {model : Foreign.Model} {before after : State}
    {event : Option Event} {context : Context} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    (step : Step program model before event after) (running : before.task = .perform context id arguments payload) :
    EffectStep program before event after := by
  rcases step with localStep | atomic | effect | control | primitive | foreign
  · cases localStep <;> simp_all
  · cases atomic <;> simp_all
  · exact effect
  · cases control <;> simp_all
  · cases primitive <;> simp_all
  · cases foreign <;> simp_all

theorem Step.completing_effect {program : Kernel.Program} {model : Foreign.Model} {before after : State}
    {event : Option Event} {context : Context} {value : Address}
    {handler : InstalledHandler} {owns : Bool} {rest : List Frame}
    (step : Step program model before event after) (running : before.task = .yield context value)
    (frames : before.frames = Frame.handler handler owns :: rest) : EffectStep program before event after := by
  rcases step with localStep | atomic | effect | control | primitive | foreign
  · cases localStep <;> simp_all
  · cases atomic <;> simp_all
  · exact effect
  · cases control <;> simp_all
  · cases primitive <;> simp_all
  · cases foreign <;> simp_all

/-- The sole execution relation consumes the source-selected terminal clause
and exposes the real pending cleanup, with no typed post-context premise. -/
theorem Step.terminal_clause_context {program : Kernel.Program} {model : Foreign.Model} {before after : State}
    {context : Context} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (handlers : ∀ handler owns, Frame.handler handler owns ∈ before.frames →
      ∃ source result, Typing.ContextBindingsTyped program before.world source handler.environment ∧
        Typing.OperationArmsType program source handler.syntaxNode.operations result)
    (running : before.task = .perform context id arguments payload)
    (step : Step program model before none after) :
    ∃ source clause inner handler owns outer roots actions, ∃ arm : Kernel.OperationArm, ∃ result locals,
      before.frames = inner ++ Frame.handler handler owns :: outer ∧
      after.frames = Frame.serviced handler owns clause none :: outer ∧
      after.task = .cleanup context roots
        (CloseRegions (inner.flatMap Frame.ownedRegions ++ [handler.computation.region])
          (.pattern clause (ScheduledPattern actions) arm.body)) ∧
      Typing.ContextBindingsTyped program after.world source clause ∧
      Typing.CodeType program (source.bindLocals locals) arm.body result ∧
      (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms clause.term) ∧
      ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope :=
  (step.performing_effect running).terminal_clause_context valid inventory worldTyped handlers running

/-- Completion dispatch is established for any actual execution step from a
yield to an installed handler. Its source environment is an input-frame fact
derived by Installs.completion_context, not an assumed output certificate. -/
theorem Step.completion_context {program : Kernel.Program} {model : Foreign.Model} {before after : State}
    {event : Option Event} {context : Context} {value : Address}
    {handler : InstalledHandler} {owns : Bool} {rest : List Frame}
    (valid : ProgramWellFormed program.declarations)
    (worldTyped : Typing.WorldTyped program before.world)
    (handlers : ∀ handler owns, Frame.handler handler owns ∈ before.frames →
      ∃ source input result, Typing.ContextBindingsTyped program before.world source handler.environment ∧
        input.Scoped source.static.scope ∧
        Typing.CompletionType program source handler.syntaxNode.completion input result)
    (running : before.task = .yield context value)
    (frames : before.frames = Frame.handler handler owns :: rest)
    (step : Step program model before event after) :
    event = none ∧ ∃ source input result clause roots,
      Typing.ContextBindingsTyped program after.world source clause ∧
      after.frames = Frame.completion handler owns clause :: rest ∧
      ((∃ kept, after.task = .cleanup context roots
          (.closeRegion handler.computation.region (.yield clause kept)) ∧
          Equal program.declarations source.static input result) ∨
        ∃ arm : Kernel.Arm, ∃ actions locals,
          after.task = .cleanup context roots
            (.closeRegion handler.computation.region (.pattern clause (ScheduledPattern actions) arm.body)) ∧
          Typing.CodeType program (source.bindLocals locals) arm.body result ∧
          (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms clause.term) ∧
          ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope) := by
  obtain ⟨source,input,result,typed,admitted,completionTyped⟩ :=
    handlers handler owns (by rw [frames]; exact List.mem_cons_self)
  obtain ⟨event,clause,roots,typed,frames,task⟩ :=
    (step.completing_effect running frames).completion_context valid worldTyped typed admitted completionTyped running frames
  exact ⟨event,source,input,result,clause,roots,typed,frames,task⟩

end Execution
end Glorious.Language
