import GloriousLanguage.ControlContextTyping
import GloriousLanguage.ForeignPreservation

/-! Actual invocation entry produces a body context or the real exhausted
prefix. Proper-tail entry preserves the newly admitted callee while scheduling
the caller's custody release, cleanup and region closure. Resident, contextual
and foreign callback recipes consume this same outcome. -/
namespace Glorious.Language.Execution

open Kernel

theorem EnterWorld.bodyTyped {program : Kernel.Program} {before : State} {caller callee : Context}
    {function : Function} {source : EntrySource} {after : World}
    (typed : Typing.FunctionType program function)
    (entered : EnterWorld program before caller function source callee after) :
    Typing.CodeType program (Typing.FunctionContext function callee.module) function.body function.signature.result := by
  obtain ⟨declaration,found,_,_,_,_,_,body⟩ := typed
  obtain ⟨_,_,_,_,selected,_,present,_,_,_,_,_,rfl,_⟩ := entered
  have same : declaration = selected := Option.some.inj (found.symm.trans present)
  subst selected
  exact body

/-- The typed observation of the actual entry transition, not an admission
premise. Failure retains precisely the exhausted binder world and consumed
fresh identities. A tail success retains the real pending custody release;
it does not assert that cleanup has already executed. -/
def FunctionEntryResult (program : Kernel.Program) (before after : State) (caller : Context)
    (function : Function) (source : EntrySource) (tail : Bool) (event : Option Event) : Prop :=
  Typing.WorldTyped program after.world ∧
  ((∃ callee,
    Typing.ContextBindingsTyped program after.world (Typing.FunctionContext function callee.module) callee ∧
    Typing.CodeType program (Typing.FunctionContext function callee.module) function.body function.signature.result ∧
    ((tail = false ∧ event = none ∧ after.task = .run callee function.body) ∨
      (tail = true ∧ event = some (.tail caller.activation callee.activation) ∧ ∃ roots regions,
        after.task = ReleaseCustodyLoans after.world (.activation caller.activation)
          (.cleanup caller roots (CloseRegions regions (.run callee function.body)))))) ∨
    (∃ callee, EnterWorldAttempt program before caller function source callee after.world .exhausted ∧
      event = some (.fatal .resource) ∧
      after = { before with
        world := after.world
        task := .fatal .resource
        nextActivation := before.nextActivation+1
        nextBrand := before.nextBrand+1 }))

theorem LocalStep.enter_function_context {program : Kernel.Program} {before after : State} {event : Option Event}
    {caller : Context} {function : Function} {source : EntrySource} {tail : Bool}
    {id : DeclId} {arguments : List Term}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (selected : Instance program id arguments function)
    (functionTyped : Typing.FunctionType program function) (formals : source.HasFormals function)
    (running : before.task = .enter caller function source tail)
    (step : LocalStep program before event after) :
    FunctionEntryResult program before after caller function source tail event := by
  refine ⟨step.worldTyped valid inventory worldTyped,?_⟩
  cases step <;> try { simp_all only [reduceCtorEq] }
  case enter actualRunning entered =>
    obtain ⟨rfl,rfl,rfl,rfl⟩ := Task.enter.inj (actualRunning.symm.trans running)
    exact Or.inl ⟨_,entered.contextBindingsTyped valid inventory worldTyped selected functionTyped formals,
      entered.bodyTyped functionTyped,Or.inl ⟨rfl,rfl,rfl⟩⟩
  case enterTail actualCaller actualFunction actualSource context enteredWorld afterWorld outer regions rest roots
      actualRunning entered relinquished _ _ _ _ =>
    obtain ⟨rfl,rfl,rfl,rfl⟩ := Task.enter.inj (actualRunning.symm.trans running)
    refine Or.inl ⟨{ context with resourceContracts := context.resourceContracts ++ actualCaller.resourceContracts },
      ?_,?_,Or.inr ⟨rfl,rfl,_,_,rfl⟩⟩
    · have retained := relinquished.contextBindingsTyped
        (entered.contextBindingsTyped valid inventory worldTyped selected functionTyped formals)
      exact { retained with }
    · have body := entered.bodyTyped functionTyped
      exact body
  case enterExhausted actualRunning attempt =>
    obtain ⟨rfl,rfl,rfl,rfl⟩ := Task.enter.inj (actualRunning.symm.trans running)
    exact Or.inr ⟨_,attempt,rfl,rfl⟩

/-- The actual call recipe supplies formal alignment even with nonempty erased
resource inputs. It does not assume successful entry or a typed output. -/
theorem LocalStep.call_then_enter_context {program : Kernel.Program} {before entering after : State}
    {id : DeclId} {inputs : List InvocationInput} {event : Option Event}
    {caller : Context} {function : Function} {source : EntrySource} {tail : Bool}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (functionTyped : Typing.FunctionType program function)
    (called : LocalStep program before (some (.call id inputs)) entering)
    (enteringTask : entering.task = .enter caller function source tail)
    (entered : LocalStep program entering event after) :
    FunctionEntryResult program entering after caller function source tail event := by
  have enteringWorld := called.worldTyped valid inventory worldTyped
  cases called with
  | call _ _ _ _ selected _ _ arguments resources =>
    obtain ⟨rfl,rfl,rfl,rfl⟩ := Task.enter.inj enteringTask
    apply entered.enter_function_context valid inventory enteringWorld selected functionTyped ?_ rfl
    simp only [EntrySource.HasFormals,List.filterMap_append,arguments.formals,resources.formals,List.append_nil]

theorem ControlStep.call_then_enter_context {program : Kernel.Program} {before entering after : State}
    {id : DeclId} {inputs : List InvocationInput} {event : Option Event}
    {caller : Context} {function : Function} {source : EntrySource} {tail : Bool}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (functionTyped : Typing.FunctionType program function)
    (called : ControlStep program before (some (.call id inputs)) entering)
    (enteringTask : entering.task = .enter caller function source tail)
    (entered : LocalStep program entering event after) :
    FunctionEntryResult program entering after caller function source tail event := by
  have enteringWorld := called.worldTyped valid inventory worldTyped
  cases called with
  | contextualCall _ _ _ _ _ _ _ selected _ _ _ _ _ captures arguments resources =>
    obtain ⟨rfl,rfl,rfl,rfl⟩ := Task.enter.inj enteringTask
    apply entered.enter_function_context valid inventory enteringWorld selected functionTyped ?_ rfl
    simp only [EntrySource.HasFormals,List.filterMap_append,captures.formals,arguments.formals,
      resources.formals,List.append_nil]

/-- Host callbacks use the same resident entry recipe, including its real
resource-failure branch; no synthetic capture list is consumed beforehand. -/
theorem _root_.Glorious.Language.Foreign.Step.callback_then_enter_context {program : Kernel.Program}
    {model : Foreign.Model} {before entering after : State} {firstEvent event : Option Event}
    {caller : Context} {function : Function} {source : EntrySource} {tail : Bool}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : model.Lawful program) (worldTyped : Typing.WorldTyped program before.world)
    (functionTyped : Typing.FunctionType program function)
    (called : Foreign.Step program model before firstEvent entering)
    (enteringTask : entering.task = .enter caller function source tail)
    (entered : LocalStep program entering event after) :
    tail = false ∧ FunctionEntryResult program entering after caller function source tail event := by
  have enteringWorld := called.worldTyped valid inventory lawful worldTyped
  cases called <;> try { cases enteringTask }
  case callback _ _ _ _ _ admitted inputs =>
    obtain ⟨rfl,rfl,rfl,rfl⟩ := Task.enter.inj enteringTask
    exact ⟨rfl,entered.enter_function_context valid inventory enteringWorld admitted.selected functionTyped
      inputs.formals rfl⟩
  case callbackResult =>
    simp only [Foreign.CallbackReturnTask] at enteringTask
    split at enteringTask <;> cases enteringTask

end Glorious.Language.Execution
