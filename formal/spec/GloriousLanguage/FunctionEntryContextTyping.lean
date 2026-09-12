import GloriousLanguage.ControlContextTyping
import GloriousLanguage.ForeignPreservation

/-! Real invocation entry consumes the source function's body typing and the
actual ordered argument/capture recipes. Ordinary and proper-tail entry share
the same newly bound callee context. Tail cleanup remains explicit. -/
namespace Glorious.Language.Execution

theorem EnterWorld.bodyTyped {program : Kernel.Program} {before : State} {caller callee : Context}
    {function : Kernel.Function} {source : EntrySource} {after : World}
    (typed : Typing.FunctionType program function)
    (entered : EnterWorld program before caller function source callee after) :
    Typing.CodeType program (Typing.FunctionContext function callee.module) function.body function.signature.result := by
  obtain ⟨declaration,found,_,_,_,_,_,body⟩ := typed
  obtain ⟨_,_,_,_,selected,present,_,_,_,rfl,_⟩ := entered
  have same : declaration = selected := Option.some.inj (found.symm.trans present)
  subst selected
  exact body

/-- The output identifies whether execution entered the body immediately or
installed it behind the actual proper-tail cleanup task. It does not hide or
assume away that cleanup obligation. -/
theorem LocalStep.enter_function_context {program : Kernel.Program} {before after : State} {event : Option Event}
    {caller : Context} {function : Kernel.Function} {source : EntrySource} {tail : Bool}
    {id : DeclId} {arguments : List Term}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (selected : Kernel.Instance program id arguments function)
    (functionTyped : Typing.FunctionType program function) (formals : source.HasFormals function)
    (running : before.task = .enter caller function source tail)
    (step : LocalStep program before event after) :
    ∃ callee,
      Typing.ContextBindingsTyped program after.world (Typing.FunctionContext function callee.module) callee ∧
      Typing.CodeType program (Typing.FunctionContext function callee.module) function.body function.signature.result ∧
      ((tail = false ∧ after.task = .run callee function.body) ∨
        (tail = true ∧ ∃ roots regions, after.task = .cleanup caller roots (CloseRegions regions (.run callee function.body)))) := by
  cases step <;> simp_all
  case enter entered =>
    exact ⟨entered.contextBindingsTyped valid inventory worldTyped selected functionTyped formals,
      entered.bodyTyped functionTyped⟩
  case enterTail entered _ _ _ _ =>
    refine ⟨_,entered.contextBindingsTyped valid inventory worldTyped selected functionTyped formals,
      entered.bodyTyped functionTyped,_,rfl⟩

/-- A real resident call constructs its formal list from the invocation's
argument recipe. The next entry therefore needs no supplied output-context
certificate or independent formal-alignment assumption. -/
theorem LocalStep.call_then_enter_context {program : Kernel.Program} {before entering after : State}
    {id : DeclId} {inputs : List Kernel.InvocationInput} {event : Option Event}
    {caller : Context} {function : Kernel.Function} {source : EntrySource} {tail : Bool}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (functionTyped : Typing.FunctionType program function)
    (called : LocalStep program before (some (.call id inputs)) entering)
    (enteringTask : entering.task = .enter caller function source tail)
    (entered : LocalStep program entering event after) :
    ∃ callee,
      Typing.ContextBindingsTyped program after.world (Typing.FunctionContext function callee.module) callee ∧
      Typing.CodeType program (Typing.FunctionContext function callee.module) function.body function.signature.result ∧
      ((tail = false ∧ after.task = .run callee function.body) ∨
        (tail = true ∧ ∃ roots regions, after.task = .cleanup caller roots (CloseRegions regions (.run callee function.body)))) := by
  cases called with
  | call _ _ _ _ selected _ _ arguments consumed =>
    simp only [Task.enter.injEq] at enteringTask
    obtain ⟨rfl,rfl,rfl,rfl⟩ := enteringTask
    apply entered.enter_function_context valid inventory (consumed.worldTyped worldTyped) selected functionTyped ?_ rfl
    exact arguments.formals

theorem ControlStep.call_then_enter_context {program : Kernel.Program} {before entering after : State}
    {id : DeclId} {inputs : List Kernel.InvocationInput} {event : Option Event}
    {caller : Context} {function : Kernel.Function} {source : EntrySource} {tail : Bool}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (functionTyped : Typing.FunctionType program function)
    (called : ControlStep program before (some (.call id inputs)) entering)
    (enteringTask : entering.task = .enter caller function source tail)
    (entered : LocalStep program entering event after) :
    ∃ callee,
      Typing.ContextBindingsTyped program after.world (Typing.FunctionContext function callee.module) callee ∧
      Typing.CodeType program (Typing.FunctionContext function callee.module) function.body function.signature.result ∧
      ((tail = false ∧ after.task = .run callee function.body) ∨
        (tail = true ∧ ∃ roots regions, after.task = .cleanup caller roots (CloseRegions regions (.run callee function.body)))) := by
  have enteringWorld := called.worldTyped valid inventory worldTyped
  cases called with
  | contextualCall _ _ _ _ _ _ selected _ _ _ _ _ _ _ _ _ _ _ _ captures arguments _ _ =>
    simp only [Task.enter.injEq] at enteringTask
    obtain ⟨rfl,rfl,rfl,rfl⟩ := enteringTask
    apply entered.enter_function_context valid inventory enteringWorld selected functionTyped ?_ rfl
    simp only [EntrySource.HasFormals,List.map_append,captures.formals,arguments.formals]

theorem _root_.Glorious.Language.Foreign.Step.callback_then_enter_context {program : Kernel.Program}
    {model : Foreign.Model} {before entering after : State} {firstEvent event : Option Event}
    {caller : Context} {function : Kernel.Function} {source : EntrySource} {tail : Bool}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (worldTyped : Typing.WorldTyped program before.world)
    (functionTyped : Typing.FunctionType program function)
    (called : Foreign.Step program model before firstEvent entering)
    (enteringTask : entering.task = .enter caller function source tail)
    (entered : LocalStep program entering event after) :
    ∃ callee,
      Typing.ContextBindingsTyped program after.world (Typing.FunctionContext function callee.module) callee ∧
      Typing.CodeType program (Typing.FunctionContext function callee.module) function.body function.signature.result ∧
      tail = false ∧ after.task = .run callee function.body := by
  have enteringWorld := called.worldTyped valid inventory lawful worldTyped
  cases called <;> simp_all
  case callback admitted _ captures arguments _ =>
    have formals : source.HasFormals function := by
      rw [← enteringTask.2.2.1]
      exact arguments.supplied_formals captures
    obtain ⟨callee,contextTyped,bodyTyped,task⟩ := entered.enter_function_context valid inventory enteringWorld admitted.selected functionTyped formals rfl
    exact ⟨callee,contextTyped,bodyTyped,by simpa using task⟩
  case callbackResult =>
    unfold Foreign.CallbackReturnTask at enteringTask
    split at enteringTask <;> cases enteringTask

end Glorious.Language.Execution
