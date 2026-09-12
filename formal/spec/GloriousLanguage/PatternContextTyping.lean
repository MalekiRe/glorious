import GloriousLanguage.ContextTyping

/-! Pattern typing's binder product is consumed in the actual scheduled
binding order. Shadowing uses the ordinary context binder, including when a
payload binder shadows a continuation or an outer local. -/
namespace Glorious.Language

private theorem constructor_field_scoped {program : Language.Program} (valid : ProgramWellFormed program)
    {data : DataDefinition} {variant : VariantDefinition} {field : FieldDefinition} {scope : LexicalScope}
    (found : program.data data.header.id = some data) (constructor : variant ∈ data.variants)
    (member : field ∈ variant.fields) : field.type.Scoped scope := by
  apply Term.ScopeClosed.scoped
  apply valid.scopeClosed (List.mem_of_find?_eq_some (Program.data_lookup found))
  simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl ⟨field,⟨variant,constructor,member⟩,rfl⟩))

/-- Borrowed binders obtain their referent scope from the actual typed
subject; nominal fields obtain it from the checked declaration substitution.
No extra output-context scope certificate is assumed. -/
theorem Typing.PatternType.locals_scoped {program : Language.Program} (valid : ProgramWellFormed program)
    {context : Language.Context} {pattern : Kernel.Pattern} {type : Term} {access : Access} {locals : List Kernel.Local}
    (typed : Typing.PatternType program context pattern type access locals)
    (admitted : type.Scoped context.scope) :
    ∀ localSlot ∈ locals, localSlot.type.Scoped context.scope := by
  refine Typing.PatternType.rec
    (motive_1 := fun _ type _ locals _ => type.Scoped context.scope →
      ∀ localSlot ∈ locals, localSlot.type.Scoped context.scope)
    (motive_2 := fun _ types _ locals _ => (∀ type ∈ types, type.Scoped context.scope) →
      ∀ localSlot ∈ locals, localSlot.type.Scoped context.scope)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed admitted
  · intro type access admitted localSlot member; cases member
  · intro localSlot type admitted equal _ other member
    simpa only [List.mem_singleton.mp member] using admitted
  · intro localSlot type mode region shape kinded admitted other member
    have same := List.mem_singleton.mp member
    subst other
    rw [shape]
    apply Term.Scoped.of_children (by simp) (by simp)
    intro child member
    simp only [Term.children,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact kinded.scoped
    · exact admitted
  · intro scalar access valid discrete admitted localSlot member; cases member
  · intro access admitted localSlot member; cases member
  · intro patterns types access locals typed ih admitted
    exact ih (fun _ member => admitted.child member)
  · intro patterns type sign width count access locals countEq typed ih admitted
    apply ih
    intro field member
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp member
    exact admitted.child (by simp only [Term.children,List.mem_cons,true_or])
  · intro id data variant arguments substitution types patterns access locals constructor visible instantiated fields typed
      disposable ih admitted
    apply ih
    intro field member
    rw [ListRel.substitutes_eq_map fields] at member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    obtain ⟨definition,inFields,rfl⟩ := List.mem_map.mp present
    apply Term.Scoped.substitute substitution definition.type
      (constructor_field_scoped valid constructor.1 constructor.2.1 inFields)
    intro parameter argument found
    exact admitted.child (instantiated.argument_of_get found)
  · intro mode region type pattern access locals typed ih admitted
    exact ih (admitted.child (by simp only [Term.children,List.mem_cons,List.not_mem_nil,or_false,or_true]))
  · intro access admitted localSlot member; cases member
  · intro pattern patterns type types access locals more first rest ihFirst ihRest admitted localSlot member
    rcases List.mem_append.mp member with first | later
    · exact ihFirst (admitted _ List.mem_cons_self) localSlot first
    · exact ihRest (fun type member => admitted type (List.mem_cons_of_mem _ member)) localSlot later

/-- This is only a projection of an already produced runtime action. It
does not infer a binder or traverse source syntax. -/
def Kernel.PatternAction.boundLocal : Kernel.PatternAction → Option Kernel.Local
  | .bind localSlot _ _ _ => some localSlot
  | .consumeShell .. | .dispose .. => none

theorem Kernel.PatternPlan.nonBinding_segments {program : Language.Program} {world : World}
    {address : Address} {authority : Authority} {access : Access} {pattern : Kernel.Pattern}
    {actions : Kernel.PatternActions}
    (planned : Kernel.PatternPlan program world address authority access pattern actions) :
    actions.shells.filterMap Kernel.PatternAction.boundLocal = [] ∧
      actions.cleanup.filterMap Kernel.PatternAction.boundLocal = [] := by
  refine Kernel.PatternPlan.rec
    (motive_1 := fun _ _ _ _ actions _ => actions.shells.filterMap Kernel.PatternAction.boundLocal = [] ∧
      actions.cleanup.filterMap Kernel.PatternAction.boundLocal = [])
    (motive_2 := fun _ _ _ _ _ actions _ => actions.shells.filterMap Kernel.PatternAction.boundLocal = [] ∧
      actions.cleanup.filterMap Kernel.PatternAction.boundLocal = [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ planned
  all_goals intros
  all_goals simp_all [Kernel.PatternAction.boundLocal]
  all_goals split <;> simp_all [Kernel.PatternAction.boundLocal]

theorem Kernel.PatternPlan.bindings_only {program : Language.Program} {world : World}
    {address : Address} {authority : Authority} {access : Access} {pattern : Kernel.Pattern}
    {actions : Kernel.PatternActions}
    (planned : Kernel.PatternPlan program world address authority access pattern actions) :
    ∀ action ∈ actions.bindings, ∃ localSlot address authority access,
      action = .bind localSlot address authority access := by
  refine Kernel.PatternPlan.rec
    (motive_1 := fun _ _ _ _ actions _ => ∀ action ∈ actions.bindings,
      ∃ localSlot address authority access, action = .bind localSlot address authority access)
    (motive_2 := fun _ _ _ _ _ actions _ => ∀ action ∈ actions.bindings,
      ∃ localSlot address authority access, action = .bind localSlot address authority access)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ planned
  all_goals intros
  all_goals simp_all
  all_goals first
  | exact ⟨_,_,_,_,rfl⟩
  | rename_i firstIH lastIH action member
    rcases member with first | later
    · exact firstIH action first
    · exact lastIH action later

theorem Typing.PatternType.plan_bindingLocals {program : Language.Program} {context : Language.Context}
    {pattern : Kernel.Pattern} {type : Term} {access : Access} {locals : List Kernel.Local}
    (typed : Typing.PatternType program context pattern type access locals) (close : Term → Term)
    {world : World} {address : Address} {authority : Authority} {actualAccess : Access} {actions : Kernel.PatternActions}
    (planned : Kernel.PatternPlan program world address authority actualAccess (pattern.mapTerms close) actions) :
    actions.bindings.filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms close) := by
  refine Typing.PatternType.rec
    (motive_1 := fun pattern _ _ locals _ => ∀ world address authority access actions,
      Kernel.PatternPlan program world address authority access (pattern.mapTerms close) actions →
      actions.bindings.filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms close))
    (motive_2 := fun patterns _ _ locals _ => ∀ world address authority access index actions,
      Kernel.PatternPlans program world address authority access index (patterns.map (Kernel.Pattern.mapTerms close)) actions →
      actions.bindings.filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms close))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed world address authority actualAccess actions planned
  · intro type access world address authority actualAccess actions planned
    simp only [Kernel.Pattern.mapTerms] at planned
    cases planned <;> simp_all
  · intro localSlot type admitted equal world address authority access actions planned
    simp only [Kernel.Pattern.mapTerms] at planned
    cases planned <;> simp_all [Kernel.PatternAction.boundLocal]
  · intro localSlot type mode region shape kinded world address authority access actions planned
    simp only [Kernel.Pattern.mapTerms] at planned
    cases planned <;> simp_all [Kernel.PatternAction.boundLocal]
  · intro scalar access valid discrete world address authority actualAccess actions planned
    simp only [Kernel.Pattern.mapTerms] at planned
    cases planned <;> simp_all
  · intro access world address authority actualAccess actions planned
    simp only [Kernel.Pattern.mapTerms] at planned
    cases planned <;> simp_all
  · intro patterns types access locals typed ih world address authority actualAccess actions planned
    simp only [Kernel.Pattern.mapTerms] at planned
    cases planned with
    | aggregate shape children =>
      rcases shape with same | same | ⟨id,same⟩
      · cases same
        have aligned := ih _ _ _ _ _ _ children
        exact aligned
      · cases same
      · cases same
  · intro patterns type sign width count access locals countEq typed ih world address authority actualAccess actions planned
    simp only [Kernel.Pattern.mapTerms] at planned
    cases planned with
    | aggregate shape children =>
      rcases shape with same | same | ⟨id,same⟩
      · cases same
      · cases same
        have aligned := ih _ _ _ _ _ _ children
        exact aligned
      · cases same
  · intro id data variant arguments substitution types patterns access locals constructor visible instantiated fields typed
      disposable ih world address authority actualAccess actions planned
    simp only [Kernel.Pattern.mapTerms] at planned
    cases planned with
    | aggregate shape children =>
      rcases shape with same | same | ⟨id,same⟩
      · cases same
      · cases same
      · cases same
        have aligned := ih _ _ _ _ _ _ children
        exact aligned
  · intro mode region type pattern access locals typed ih world address authority actualAccess actions planned
    simp only [Kernel.Pattern.mapTerms] at planned
    cases planned with
    | aggregate shape _ => rcases shape with same | same | ⟨id,same⟩ <;> cases same
    | reference _ _ _ _ _ _ _ _ child =>
      have aligned := ih _ _ _ _ _ child
      exact aligned
  · intro access world address authority actualAccess index actions planned
    cases planned; rfl
  · intro pattern patterns type types access locals more first rest ihFirst ihRest world address authority actualAccess index actions planned
    cases planned with
    | cons first rest =>
      simp only [List.filterMap_append,List.map_append,ihFirst _ _ _ _ _ first,ihRest _ _ _ _ _ _ rest]

/-- The source binder list is exactly the bind subsequence of the real
scheduled actions; shell and cleanup scheduling cannot reorder it. -/
theorem Typing.PatternType.scheduled_bindingLocals {program : Language.Program} {context : Language.Context}
    {pattern : Kernel.Pattern} {type : Term} {access : Access} {locals : List Kernel.Local}
    (typed : Typing.PatternType program context pattern type access locals) (close : Term → Term)
    {world : World} {address : Address} {authority : Authority} {actualAccess : Access} {actions : Kernel.PatternActions}
    (planned : Kernel.PatternPlan program world address authority actualAccess (pattern.mapTerms close) actions) :
    (Execution.ScheduledPattern actions).filterMap Kernel.PatternAction.boundLocal =
      locals.map (Kernel.Local.mapTerms close) := by
  have noBinders := planned.nonBinding_segments
  simp only [Execution.ScheduledPattern,List.filterMap_append,noBinders.1,noBinders.2,
    List.nil_append,List.append_nil,typed.plan_bindingLocals close planned]

theorem Typing.PatternType.first_binding {program : Language.Program} {context : Language.Context}
    {pattern : Kernel.Pattern} {type : Term} {access : Access} {localSlot : Kernel.Local} {locals : List Kernel.Local}
    (typed : Typing.PatternType program context pattern type access (localSlot :: locals)) (close : Term → Term)
    {world : World} {address : Address} {authority : Authority} {actualAccess : Access} {actions : Kernel.PatternActions}
    (planned : Kernel.PatternPlan program world address authority actualAccess (pattern.mapTerms close) actions) :
    ∃ source permission access rest,
      actions.bindings = .bind (localSlot.mapTerms close) source permission access :: rest ∧
      rest.filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms close) := by
  have ordered := typed.plan_bindingLocals close planned
  cases selected : actions.bindings with
  | nil => simp only [selected,List.filterMap_nil,List.map_cons] at ordered; cases ordered
  | cons first rest =>
    obtain ⟨actual,source,permission,access,rfl⟩ := planned.bindings_only first (by rw [selected]; exact List.mem_cons_self)
    simp only [selected,List.filterMap_cons,Kernel.PatternAction.boundLocal,List.map_cons] at ordered
    obtain ⟨rfl,tail⟩ := List.cons.inj ordered
    exact ⟨source,permission,access,rest,rfl,tail⟩

/-- One actual pattern binding advances the same fold used by ArmsType and
OperationArmsType. The body retains its original typing derivation. -/
theorem Execution.LocalStep.patternBind_context {program : Kernel.Program} {before : Execution.State}
    {source : Typing.Context} {runtime : Execution.Context} {lexical : Kernel.Local}
    {remainingLocals : List Kernel.Local} {address : Address} {authority : Authority} {access : Access}
    {binding : Kernel.Binding} {after : World} {rest : List Kernel.PatternAction} {body : Kernel.Code} {result : Term}
    (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source runtime)
    (admitted : lexical.type.Scoped source.static.scope)
    (bodyTyped : Typing.CodeType program (source.bindLocals (lexical :: remainingLocals)) body result)
    (running : before.task = .pattern runtime (.bind (runtime.local lexical) address authority access :: rest) body)
    (bound : Kernel.BindsPattern program.declarations runtime.activation runtime.scope runtime.region before.world
      (runtime.local lexical) address authority access binding after) :
    Execution.LocalStep program before none
      { before with world := after, task := .pattern (runtime.bind (runtime.local lexical) binding.address binding.authority) rest body } ∧
    Typing.ContextBindingsTyped program after (source.bind lexical)
      (runtime.bind (runtime.local lexical) binding.address binding.authority) ∧
    Typing.CodeType program ((source.bind lexical).bindLocals remainingLocals) body result :=
  ⟨.patternBind running bound,bound.contextBindingsTyped worldTyped typed admitted,bodyTyped⟩

/-- At the real binding segment, neither its first lexical binder nor its
scope admission is supplied separately: both come from the source pattern
and the actual plan. The executed step advances the same body-context fold. -/
theorem Execution.LocalStep.plannedPatternBind_context {program : Kernel.Program}
    {before after : Execution.State} {event : Option Execution.Event} {planningWorld : World}
    {source : Typing.Context} {runtime : Execution.Context} {lexical : Kernel.Local} {locals : List Kernel.Local}
    {pattern : Kernel.Pattern} {type : Term} {access actualAccess : Access} {address : Address} {authority : Authority}
    {actions : Kernel.PatternActions} {body : Kernel.Code} {result : Term}
    (valid : ProgramWellFormed program.declarations) (worldTyped : Typing.WorldTyped program before.world)
    (typed : Typing.ContextBindingsTyped program before.world source runtime)
    (patternTyped : Typing.PatternType program.declarations source.static pattern type access (lexical :: locals))
    (admitted : type.Scoped source.static.scope)
    (planned : Kernel.PatternPlan program.declarations planningWorld address authority actualAccess (pattern.mapTerms runtime.term) actions)
    (bodyTyped : Typing.CodeType program (source.bindLocals (lexical :: locals)) body result)
    (running : before.task = .pattern runtime (actions.bindings ++ actions.cleanup) body)
    (step : Execution.LocalStep program before event after) :
    ∃ inner rest, after.task = .pattern inner rest body ∧
      Typing.ContextBindingsTyped program after.world (source.bind lexical) inner ∧
      rest.filterMap Kernel.PatternAction.boundLocal = locals.map (Kernel.Local.mapTerms runtime.term) ∧
      Typing.CodeType program ((source.bind lexical).bindLocals locals) body result := by
  obtain ⟨address,authority,access,rest,first,remaining⟩ := patternTyped.first_binding runtime.term planned
  have noBinders := planned.nonBinding_segments
  have ordered : (rest ++ actions.cleanup).filterMap Kernel.PatternAction.boundLocal =
      locals.map (Kernel.Local.mapTerms runtime.term) := by
    rw [List.filterMap_append,remaining,noBinders.2,List.append_nil]
  have localScoped := patternTyped.locals_scoped valid admitted lexical List.mem_cons_self
  rw [first,List.cons_append] at running
  cases step <;> simp_all
  refine ⟨_,_,⟨rfl,rfl⟩,?_,?_,bodyTyped⟩
  · exact (‹Kernel.BindsPattern _ _ _ _ _ _ _ _ _ _ _›).contextBindingsTyped worldTyped typed localScoped
  · rw [List.filterMap_append,remaining]
    simp_all

end Glorious.Language
