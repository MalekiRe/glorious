import GloriousLanguage.ClauseEntryContextTyping

/-! Actual ordered match selection consumes source projection scope and the
selected arm's one binder product. The first executed action advances that
same product; pending destruction is retained as an explicit continuation. -/
namespace Glorious.Language.Execution

theorem _root_.Glorious.Language.Typing.CodeType.choose_arm
    {program : Kernel.Program} {context : Typing.Context} {code : Kernel.Code} {result : Term}
    (typed : Typing.CodeType program context code result) :
    ∀ subject arms, code = .choose subject arms → ∀ arm ∈ arms,
      ∃ type writable locals,
        Typing.PlaceType program.declarations context subject type writable ∧
        Typing.PatternType program.declarations context.static arm.pattern type .owned locals ∧
        Typing.CodeType program (context.bindLocals locals) arm.body result := by
  refine Typing.CodeType.rec
    (motive_1 := fun context code result _ => ∀ subject arms, code = .choose subject arms → ∀ arm ∈ arms,
      ∃ type writable locals,
        Typing.PlaceType program.declarations context subject type writable ∧
        Typing.PatternType program.declarations context.static arm.pattern type .owned locals ∧
        Typing.CodeType program (context.bindLocals locals) arm.body result)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  all_goals intros
  all_goals try exact True.intro
  all_goals try (solve | cases ‹_ = Kernel.Code.choose _ _›)
  case refine_10 =>
    rename_i armsTyped _ subject arms same arm member
    rcases Kernel.Code.choose.inj same with ⟨rfl,rfl⟩
    obtain ⟨locals,patternTyped,bodyTyped⟩ := armsTyped.member member
    exact ⟨_,_,locals,‹Typing.PlaceType _ _ _ _ _›,patternTyped,bodyTyped⟩
  case refine_18 =>
    rename_i admitted _ ih subject arms same arm member
    obtain ⟨type,writable,locals,place,patternTyped,bodyTyped⟩ := ih subject arms same arm member
    exact ⟨type,writable,locals,place,patternTyped,
      Typing.CodeType.bottom (by simpa only [Typing.Context.bindLocals_static] using admitted) bodyTyped⟩

theorem Step.choosing_local {program : Kernel.Program} {model : Foreign.Model}
    {before after : State} {event : Option Event} {runtime : Context}
    {subject : Kernel.Place} {arms : List Kernel.Arm}
    (step : Step program model before event after)
    (running : before.task = .run runtime (.choose subject arms)) : LocalStep program before event after := by
  rcases step with localStep | atomic | effect | control | primitive | foreign
  · exact localStep
  · cases atomic <;> simp_all
  · cases effect <;> simp_all
  · cases control <;> simp_all
  · cases primitive <;> simp_all
  · cases foreign <;> simp_all

theorem LocalStep.choose_context {program : Kernel.Program} {before after : State} {event : Option Event}
    {source : Typing.Context} {runtime : Context} {subject : Kernel.Place} {arms : List Kernel.Arm} {code : Kernel.Code} {result : Term}
    (valid : ProgramWellFormed program.declarations)
    (contextTyped : Typing.ContextBindingsTyped program before.world source runtime)
    (codeTyped : Typing.CodeType program source code result) (choosing : code = .choose subject arms)
    (running : before.task = .run runtime (.choose subject arms))
    (step : LocalStep program before event after) :
    event = none ∧ ∃ arm : Kernel.Arm, ∃ actions locals,
      arm ∈ arms ∧
      after.task = .pattern runtime (ScheduledPattern actions) arm.body ∧
      after.frames = before.frames ∧
      Typing.ContextBindingsTyped program after.world source runtime ∧
      Typing.CodeType program (source.bindLocals locals) arm.body result ∧
      (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal =
        locals.map (Kernel.Local.mapTerms runtime.term) ∧
      ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope := by
  cases step <;> try (solve | simp_all)
  case choose running' _ selected planned =>
    rcases Task.run.inj (running'.symm.trans running) with ⟨rfl,sameCode⟩
    rcases Kernel.Code.choose.inj sameCode with ⟨rfl,rfl⟩
    obtain ⟨_,_,locals,place,patternTyped,bodyTyped⟩ := codeTyped.choose_arm _ _ choosing _ selected.member
    have admitted := contextTyped.place_scoped valid place
    exact ⟨rfl,_,_,locals,selected.member,rfl,rfl,contextTyped,bodyTyped,
      patternTyped.scheduled_bindingLocals _ planned,patternTyped.locals_scoped valid admitted⟩

theorem Step.choose_context {program : Kernel.Program} {model : Foreign.Model}
    {before after : State} {event : Option Event} {source : Typing.Context} {runtime : Context}
    {subject : Kernel.Place} {arms : List Kernel.Arm} {result : Term}
    (valid : ProgramWellFormed program.declarations)
    (contextTyped : Typing.ContextBindingsTyped program before.world source runtime)
    (codeTyped : Typing.CodeType program source (.choose subject arms) result)
    (running : before.task = .run runtime (.choose subject arms))
    (step : Step program model before event after) :
    event = none ∧ ∃ arm : Kernel.Arm, ∃ actions locals,
      arm ∈ arms ∧
      after.task = .pattern runtime (ScheduledPattern actions) arm.body ∧
      after.frames = before.frames ∧
      Typing.ContextBindingsTyped program after.world source runtime ∧
      Typing.CodeType program (source.bindLocals locals) arm.body result ∧
      (ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal =
        locals.map (Kernel.Local.mapTerms runtime.term) ∧
      ∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope :=
  (step.choosing_local running).choose_context valid contextTyped codeTyped rfl running

/-- Scope of the borrowed subject and every emitted local comes from actual
function/context/projection admission. Nothing here assumes that the pattern
machine's next context or its chosen reference referent is already scoped. -/
theorem Step.chosen_arm_first_step {program : Kernel.Program} {model : Foreign.Model}
    {before middle after : State} {choiceEvent event : Option Event} {source : Typing.Context} {runtime : Context}
    {subject : Kernel.Place} {arms : List Kernel.Arm} {result : Term}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (contextTyped : Typing.ContextBindingsTyped program before.world source runtime)
    (codeTyped : Typing.CodeType program source (.choose subject arms) result)
    (running : before.task = .run runtime (.choose subject arms))
    (chosen : Step program model before choiceEvent middle)
    (advanced : Step program model middle event after) :
    ∃ arm : Kernel.Arm, ∃ nextSource nextRuntime remaining,
      arm ∈ arms ∧
      Typing.ContextBindingsTyped program after.world nextSource nextRuntime ∧
      Typing.CodeType program (nextSource.bindLocals remaining) arm.body result ∧
      (∀ localSlot ∈ remaining, localSlot.type.Scoped nextSource.static.scope) ∧
      ((∃ rest, after.task = .pattern nextRuntime rest arm.body ∧
          rest.filterMap Kernel.PatternAction.boundLocal = remaining.map (Kernel.Local.mapTerms nextRuntime.term)) ∨
        (after.task = .run nextRuntime arm.body ∧ remaining = []) ∨
        ∃ address authority rest, after.task = .destroy nextRuntime address authority (.pattern nextRuntime rest arm.body) ∧
          rest.filterMap Kernel.PatternAction.boundLocal = remaining.map (Kernel.Local.mapTerms nextRuntime.term)) := by
  obtain ⟨_,arm,actions,locals,member,task,_,entered,bodyTyped,binders,admitted⟩ :=
    chosen.choose_context valid contextTyped codeTyped running
  obtain ⟨nextSource,nextRuntime,remaining,typed,body,admitted,task⟩ :=
    (advanced.pattern_local task).pattern_context
      ((chosen.choosing_local running).worldTyped valid inventory worldTyped) entered bodyTyped binders admitted task
  exact ⟨arm,nextSource,nextRuntime,remaining,member,typed,body,admitted,task⟩

end Glorious.Language.Execution
