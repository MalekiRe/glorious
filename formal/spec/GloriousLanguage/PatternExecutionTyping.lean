import GloriousLanguage.OperationContextTyping

/-! The machine consumes the ordered binder product already established by
source pattern typing. No pattern is reanalysed while actions execute. A
destructor is scheduled explicitly; its later lifetime proof is not assumed. -/
namespace Glorious.Language

theorem Deconstructs.bindingStorageTyped {program : RuntimeProgram} {context : Language.Context} {before after : World}
    {authority : Authority} {address : Address} (valid : before.WellFormed)
    (consumed : Deconstructs program context before authority address after)
    {observed : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before observed type) :
    Typing.BindingStorageTyped program.declarations after observed type := by
  cases consumed with
  | shell stored _ permission _ _ written => exact World.write_shell_bindingStorageTyped valid stored permission written binding

namespace Execution

theorem Step.pattern_local {program : Kernel.Program} {model : Foreign.Model} {before after : State} {event : Option Event}
    {runtime : Context} {actions : List Kernel.PatternAction} {body : Kernel.Code}
    (step : Step program model before event after) (running : before.task = .pattern runtime actions body) :
    LocalStep program before event after := by
  rcases step with localStep | atomic | effect | control | primitive | foreign
  · exact localStep
  · cases atomic <;> simp_all
  · cases effect <;> simp_all
  · cases control <;> simp_all
  · cases primitive <;> simp_all
  · cases foreign <;> simp_all

theorem Step.suspending_effect {program : Kernel.Program} {model : Foreign.Model} {before after : State} {id : Identity}
    (step : Step program model before (some (.suspend id)) after) : EffectStep program before (some (.suspend id)) after := by
  rcases step with localStep | atomic | effect | control | primitive | foreign
  · cases localStep
  · generalize equation : some (Event.suspend id) = event at atomic
    cases atomic <;> simp_all
    all_goals split at equation <;> simp_all
    all_goals split at equation <;> simp_all
  · exact effect
  · cases control
  · cases primitive
  · cases foreign

/-- One step of the actual pattern machine advances only its emitted binder
cursor. Shell consumption preserves the cursor; disposal exposes its pending
continuation instead of claiming that arbitrary destruction preserves it. -/
theorem LocalStep.pattern_context {program : Kernel.Program} {before after : State} {event : Option Event}
    {source : Typing.Context} {runtime : Context} {actions : List Kernel.PatternAction}
    {body : Kernel.Code} {locals : List Kernel.Local} {result : Term}
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source runtime)
    (bodyTyped : Typing.CodeType program (source.bindLocals locals) body result)
    (binders : actions.filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms runtime.term))
    (admitted : ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope)
    (running : before.task = .pattern runtime actions body) (step : LocalStep program before event after) :
    ∃ nextSource nextRuntime remaining,
      Typing.ContextBindingsTyped program after.world nextSource nextRuntime ∧
      Typing.CodeType program (nextSource.bindLocals remaining) body result ∧
      (∀ localSlot ∈ remaining, localSlot.type.Scoped nextSource.static.scope) ∧
      ((∃ rest, after.task = .pattern nextRuntime rest body ∧
          rest.filterMap Kernel.PatternAction.boundLocal = remaining.map (Kernel.Local.mapTerms nextRuntime.term)) ∨
        (after.task = .run nextRuntime body ∧ remaining = []) ∨
        ∃ address authority rest, after.task = .destroy nextRuntime address authority (.pattern nextRuntime rest body) ∧
          rest.filterMap Kernel.PatternAction.boundLocal = remaining.map (Kernel.Local.mapTerms nextRuntime.term)) := by
  cases step <;> simp_all
  case patternDone =>
    have empty : locals = [] := binders
    subst locals
    exact ⟨source,runtime,typed,[],bodyTyped,by simp,rfl,rfl⟩
  case patternBind bound =>
    rw [← running.2.1] at binders
    simp only [List.filterMap_cons,Kernel.PatternAction.boundLocal] at binders
    cases locals with
    | nil => simp at binders
    | cons lexical remaining =>
      have aligned := List.cons.inj binders
      have localEq : _ = runtime.local lexical := aligned.1
      rw [localEq] at bound
      rw [localEq]
      have nextContext := bound.contextBindingsTyped worldTyped typed (admitted lexical List.mem_cons_self)
      refine ⟨source.bind lexical,_,nextContext,remaining,bodyTyped,?_,_,⟨rfl,rfl⟩,?_⟩
      · exact fun localSlot member => admitted localSlot (List.mem_cons_of_mem _ member)
      · exact aligned.2
  case patternShell consumed =>
    rw [← running.2.1] at binders
    simp only [List.filterMap_cons,Kernel.PatternAction.boundLocal] at binders
    exact ⟨source,runtime,typed.world (fun _ _ binding => consumed.bindingStorageTyped worldTyped.1 binding),
      locals,bodyTyped,admitted,_,⟨rfl,rfl⟩,binders⟩
  case patternDispose =>
    rw [← running.2.1] at binders
    simp only [List.filterMap_cons,Kernel.PatternAction.boundLocal] at binders
    exact ⟨source,runtime,typed,locals,bodyTyped,admitted,_,_,_,⟨rfl,rfl,rfl,rfl,rfl⟩,binders⟩

/-- The actual suspension entry feeds its source-derived binder product
directly into the first machine pattern step, including aggregate shells and
scheduled destructor work. -/
theorem Step.suspended_clause_first_step {program : Kernel.Program} {model : Foreign.Model} {before middle after : State}
    {id : Identity} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (handlers : ∀ handler owns, Frame.handler handler owns ∈ before.frames →
      Typing.InstalledHandlerTyped program before.world handler)
    (suspended : Step program model before (some (.suspend id)) middle)
    (advanced : Step program model middle event after) :
    ∃ source runtime locals body result,
      Typing.ContextBindingsTyped program after.world source runtime ∧
      Typing.CodeType program (source.bindLocals locals) body result ∧
      (∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope) ∧
      ((∃ rest, after.task = .pattern runtime rest body ∧
          rest.filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms runtime.term)) ∨
        (after.task = .run runtime body ∧ locals = []) ∨
        ∃ address authority rest, after.task = .destroy runtime address authority (.pattern runtime rest body) ∧
          rest.filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms runtime.term)) := by
  have suspended := suspended.suspending_effect
  obtain ⟨source,runtime,actions,body,locals,result,running,contextTyped,bodyTyped,binders,admitted⟩ :=
    suspended.suspended_clause_context valid inventory worldTyped handlers
  obtain ⟨nextSource,nextRuntime,remaining,contextTyped,bodyTyped,admitted,task⟩ :=
    (advanced.pattern_local running).pattern_context
      (suspended.worldTyped valid inventory worldTyped) contextTyped bodyTyped binders admitted running
  exact ⟨nextSource,nextRuntime,remaining,body,result,contextTyped,bodyTyped,admitted,task⟩

end Execution
end Glorious.Language
