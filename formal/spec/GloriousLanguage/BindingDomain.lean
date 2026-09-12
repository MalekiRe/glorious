import GloriousLanguage.Machine

/-! Source locals are the local-key projection of the common runtime binding
domain. Erased resource ports remain in that domain, but do not impersonate
source locals or require initialized resident storage. -/
namespace Glorious.Language.Kernel

def Environment.locals (environment : Environment) : Environment :=
  environment.filter fun binding => match binding.key with
    | .localSlot _ => true
    | .resourceInput _ | .obligation _ => false

theorem Environment.mem_locals {environment : Environment} {binding : Binding} :
    binding ∈ environment.locals ↔ binding ∈ environment ∧ ∃ identity, binding.key = .localSlot identity := by
  cases key : binding.key <;> simp [Environment.locals,key]

theorem Environment.selects_locals_iff {environment : Environment} {identity : Identity} {binding : Binding} :
    environment.locals.Selects identity binding ↔ environment.Selects identity binding := by
  constructor
  · intro selected
    refine ⟨(Environment.mem_locals.mp selected.1).1,selected.2.1,?_⟩
    intro other member key
    exact selected.2.2 other (Environment.mem_locals.mpr ⟨member,identity,key⟩) key
  · intro selected
    refine ⟨Environment.mem_locals.mpr ⟨selected.1,identity,selected.2.1⟩,selected.2.1,?_⟩
    intro other member key
    exact selected.2.2 other (Environment.mem_locals.mp member).1 key

theorem Environment.locals_filter (environment : Environment) (keep : Binding → Bool) :
    Environment.locals (environment.filter keep) = environment.locals.filter keep := by
  simp only [Environment.locals,List.filter_filter]
  congr 1
  funext binding
  exact Bool.and_comm _ _

/-- Unique selection uses real binding keys, including resource-port keys.
The source-local view below merely restricts this same selection relation. -/
theorem Environment.selectsKey_of_nodup {environment : Environment} {binding : Binding}
    (distinct : (environment.map (·.key)).Nodup) (member : binding ∈ environment) :
    environment.SelectsKey binding.key binding := by
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
        simpa only [same] using (List.mem_map.mpr ⟨other,otherInRest,rfl⟩ : other.key ∈ rest.map (·.key))
    · rcases List.mem_cons.mp present with rfl | otherInRest
      · apply False.elim; apply separated.1
        simpa only [same] using (List.mem_map.mpr ⟨binding,bindingInRest,rfl⟩ : binding.key ∈ rest.map (·.key))
      · exact ih separated.2 bindingInRest otherInRest

theorem Environment.selects_local_of_related {environment : Environment} {locals : List Local}
    {relation : Local → Binding → Prop}
    (paired : ListRel (fun localSlot binding => binding.key = .localSlot localSlot.id ∧
      relation localSlot binding) locals environment.locals)
    (distinct : (locals.map (·.id)).Nodup) {localSlot : Local} (member : localSlot ∈ locals) :
    ∃ binding, environment.Selects localSlot.id binding ∧ relation localSlot binding := by
  have keys : environment.locals.map (·.key) = (locals.map (·.id)).map BindingKey.localSlot := by
    clear distinct member
    generalize environment.locals = bindings at paired ⊢
    induction paired with
    | nil => rfl
    | cons head _ ih => simp only [List.map_cons,head.1,ih]
  have unique : (environment.locals.map (·.key)).Nodup := by
    rw [keys]
    exact distinct.map BindingKey.localSlot (fun _ _ different equal => different (BindingKey.localSlot.inj equal))
  obtain ⟨binding,present,key,related⟩ := paired.member_left member
  refine ⟨binding,Environment.selects_locals_iff.mp ?_,related⟩
  have selected := Environment.selectsKey_of_nodup unique present
  rw [key] at selected
  exact selected

/-- Filtering the actual paired input/binding product retains exactly its
resident formals. Raw storage, allocation and loan ports are erased only from
the source-local view, never from the runtime environment. -/
theorem _root_.Glorious.Language.ListRel.resident_inputs {relation : Local → Binding → Prop}
    {inputs : List InvocationInput} {bindings : Environment}
    (paired : Glorious.Language.ListRel (fun input binding => binding.key = input.formal.key ∧
      ∀ localSlot, input.formal = .resident localSlot → relation localSlot binding) inputs bindings) :
    Glorious.Language.ListRel relation (inputs.filterMap (fun input => input.formal.resident?)) bindings.locals := by
  induction paired with
  | nil => exact .nil
  | @cons input binding inputs bindings head tail ih =>
    cases formal : input.formal with
    | resident localSlot =>
        have key : binding.key = .localSlot localSlot.id := by simpa only [formal,InputFormal.key] using head.1
        simpa [formal,InputFormal.resident?,Environment.locals,key] using
          Glorious.Language.ListRel.cons (head.2 localSlot formal) ih
    | storage identity type | allocation identity type | loan identity type =>
        have key : binding.key = .resourceInput identity := by simpa only [formal,InputFormal.key] using head.1
        simpa [formal,InputFormal.resident?,Environment.locals,key] using ih

end Glorious.Language.Kernel
