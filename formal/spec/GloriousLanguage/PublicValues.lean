import GloriousLanguage.SemanticPreservation

/-! Complete logical observations of initialized typed residents. References
observe the existing loan's referent, without unfolding a potentially cyclic
storage graph. Callable and binding-pack fields use the very same recursive
observation as ordinary aggregates; their resident payload is not erased.
Lifetime escape remains governed by execution and resource admission. -/
namespace Glorious.Language

theorem Value.Initialized.child {parent child : Value}
    (initialized : parent.Initialized) (member : some child ∈ parent.fields) : child.Initialized := by
  obtain ⟨index,bound,found⟩ := List.mem_iff_getElem.mp member
  intro path value resident
  exact initialized (index :: path) value (.field (by simpa [found] using List.getElem?_eq_getElem bound) resident)

theorem Value.initialized_iff {value : Value} : value.Initialized ↔
    value.shellLive = true ∧
      ∀ field ∈ value.fields, ∃ child, field = some child ∧ child.Initialized := by
  constructor
  · intro initialized
    refine ⟨(initialized [] value .root).1,?_⟩
    intro field member
    obtain ⟨child,same⟩ := Option.isSome_iff_exists.mp ((initialized [] value .root).2 field member)
    exact ⟨child,same,initialized.child (same ▸ member)⟩
  · rintro ⟨live,fields⟩ path resident nested
    cases nested with
    | root =>
      refine ⟨live,?_⟩
      intro field member
      obtain ⟨child,rfl,_⟩ := fields field member
      rfl
    | @field value index child path resident found nested =>
      have member : some child ∈ value.fields := List.mem_of_getElem? found
      obtain ⟨other,same,initialized⟩ := fields (some child) member
      have equal : child = other := Option.some.inj same
      subst other
      exact initialized path resident nested

namespace Specification

/-- The observer does not manufacture an alternative value or erase a live
capture: its output is uniquely determined by the actual resident and loans. -/
theorem Reveals.functional {world : World} {value : Value} {first last : PublicValue}
    (left : Reveals world value first) (right : Reveals world value last) : first = last := by
  refine Reveals.rec
    (motive_1 := fun value observed _ => ∀ other, Reveals world value other → observed = other)
    (motive_2 := fun fields observed _ => ∀ other, RevealsFields world fields other → observed = other)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ left last right
  · intro owner resources other revealed
    cases revealed <;> simp_all
  · intro owner scalar resources other revealed
    generalize typeEq : Term.scalar scalar.type = type at revealed
    cases revealed <;> simp_all
  · intro owner type head fields values variant resources shape _ ih other revealed
    rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨id,rfl,rfl⟩ <;>
      cases revealed with
      | aggregate otherShape otherFields =>
        simp_all
        exact ih _ otherFields
  · intro owner type id loan resources found active other revealed
    cases revealed with
    | reference selected _ =>
      have same := Option.some.inj (found.symm.trans selected)
      cases same
      rfl
    | aggregate shape _ => simp at shape
  · intro owner type pointer resources other revealed
    cases revealed <;> simp_all
  · intro owner type id arguments fields captures resources _ ih other revealed
    cases revealed with
    | callable fields => rw [ih _ fields]
    | aggregate shape _ => simp at shape
  · intro owner type id arguments resources other revealed
    cases revealed <;> simp_all
  · intro owner type brand resources other revealed
    cases revealed <;> simp_all
  · intro owner type id resources other revealed
    cases revealed <;> simp_all
  · intro owner type id resources other revealed
    cases revealed <;> simp_all
  · intro owner type pack fields values resources _ ih other revealed
    cases revealed with
    | bindings fields => rw [ih _ fields]
    | aggregate shape _ => simp at shape
  · intro other revealed
    cases revealed
    rfl
  · intro value values observed observations _ _ ih tail other revealed
    cases revealed with
    | cons head rest => rw [ih _ head,tail _ rest]

theorem Reveals.initialized {world : World} {value : Value} {observed : PublicValue}
    (revealed : Reveals world value observed) : value.Initialized := by
  refine Reveals.rec
    (motive_1 := fun value _ _ => value.Initialized)
    (motive_2 := fun fields _ _ => ∀ field ∈ fields, ∃ child, field = some child ∧ child.Initialized)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ revealed
  · intro owner resources
    exact Value.initialized_iff.mpr ⟨rfl,by simp [Value.fields]⟩
  · intro owner scalar resources
    exact Value.initialized_iff.mpr ⟨rfl,by simp [Value.fields]⟩
  · intro owner type head fields values variant resources shape revealed ih
    exact Value.initialized_iff.mpr ⟨rfl,ih⟩
  · intro owner type id loan resources found active
    exact Value.initialized_iff.mpr ⟨rfl,by simp [Value.fields]⟩
  · intro owner type pointer resources
    exact Value.initialized_iff.mpr ⟨rfl,by simp [Value.fields]⟩
  · intro owner type id arguments fields captures resources revealed ih
    exact Value.initialized_iff.mpr ⟨rfl,ih⟩
  · intro owner type id arguments resources
    exact Value.initialized_iff.mpr ⟨rfl,by simp [Value.fields]⟩
  · intro owner type brand resources
    exact Value.initialized_iff.mpr ⟨rfl,by simp [Value.fields]⟩
  · intro owner type id resources
    exact Value.initialized_iff.mpr ⟨rfl,by simp [Value.fields]⟩
  · intro owner type id resources
    exact Value.initialized_iff.mpr ⟨rfl,by simp [Value.fields]⟩
  · intro owner type pack fields values resources revealed ih
    exact Value.initialized_iff.mpr ⟨rfl,ih⟩
  · simp
  · intro value values observed observations revealed fields ih tail field member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨value,rfl,ih⟩
    · exact tail field member

theorem valueTyped_reveals {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) (initialized : value.Initialized) :
    ∃ observed, Reveals world value observed := by
  refine Typing.ValueTyped.rec
    (motive_1 := fun value _ => value.Initialized → ∃ observed, Reveals world value observed)
    (motive_2 := fun fields _ _ =>
      (∀ field ∈ fields, ∃ child, field = some child ∧ child.Initialized) →
        ∃ observed, RevealsFields world fields observed)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed initialized
  · intro owner live initialized
    have same := (initialized [] _ .root).1
    cases same
    exact ⟨_,.unit⟩
  · intro owner value live valid initialized
    have same := (initialized [] _ .root).1
    cases same
    exact ⟨_,.scalar⟩
  · intro owner type head live fields types resources shape _ ih initialized
    obtain ⟨active,fieldsLive⟩ := Value.initialized_iff.mp initialized
    change live = true at active
    subst live
    obtain ⟨observed,revealed⟩ := ih fieldsLive
    rcases shape with ⟨_,_,head⟩ | ⟨_,_,_,_,_,_,head,_,_⟩ | ⟨_,_,_,_,_,_,_,head,_,_,_⟩
    · exact ⟨_,.aggregate (Or.inl ⟨head,rfl⟩) revealed⟩
    · exact ⟨_,.aggregate (Or.inr (Or.inl ⟨head,rfl⟩)) revealed⟩
    · exact ⟨_,.aggregate (Or.inr (Or.inr ⟨_,head,rfl⟩)) revealed⟩
  · intro owner mode region type id loan live found active modeEq regionEq address initialized
    have same := (initialized [] _ .root).1
    cases same
    exact ⟨_,.reference found active⟩
  · intro owner mode type pointer live bound origin initialized
    have same := (initialized [] _ .root).1
    cases same
    exact ⟨_,.pointer⟩
  · intro owner id arguments live fields function selected _ ih initialized
    obtain ⟨active,fieldsLive⟩ := Value.initialized_iff.mp initialized
    change live = true at active
    subst live
    obtain ⟨captures,revealed⟩ := ih fieldsLive
    exact ⟨_,.callable revealed⟩
  · intro owner id arguments live operation signature selected initialized
    have same := (initialized [] _ .root).1
    cases same
    exact ⟨_,.operation⟩
  · intro owner brand region result live initialized
    have same := (initialized [] _ .root).1
    cases same
    exact ⟨_,.label⟩
  · intro owner type id live typeEq initialized
    have same := (initialized [] _ .root).1
    cases same
    exact ⟨_,.continuation⟩
  · intro owner brand region residents id live available found brandEq idEq regionEq residentsEq initialized
    have same := (initialized [] _ .root).1
    cases same
    exact ⟨_,.available⟩
  · intro owner brand region live fields types pack _ brandEq regionEq length distinct ih initialized
    obtain ⟨active,fieldsLive⟩ := Value.initialized_iff.mp initialized
    change live = true at active
    subst live
    obtain ⟨observed,revealed⟩ := ih fieldsLive
    exact ⟨_,.bindings revealed⟩
  · intro _
    exact ⟨[],.nil⟩
  · intro fields type types typed ih initialized
    obtain ⟨_,impossible,_⟩ := initialized none (by simp)
    cases impossible
  · intro value fields type types valueTyped typeEq fieldsTyped ih tail initialized
    obtain ⟨child,same,active⟩ := initialized (some value) (by simp)
    have equal : child = value := (Option.some.inj same).symm
    subst child
    obtain ⟨observed,revealed⟩ := ih active
    obtain ⟨more,rest⟩ := tail (fun field member => initialized field (List.mem_cons_of_mem _ member))
    exact ⟨observed :: more,.cons revealed rest⟩

theorem valueTyped_reveals_iff {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) :
    (∃ observed, Reveals world value observed) ↔ value.Initialized := by
  constructor
  · rintro ⟨observed,revealed⟩
    exact revealed.initialized
  · exact valueTyped_reveals typed

theorem valueTyped_reveals_unique {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) (initialized : value.Initialized) :
    ∃ observed, Reveals world value observed ∧ ∀ other, Reveals world value other → other = observed := by
  obtain ⟨observed,revealed⟩ := valueTyped_reveals typed initialized
  exact ⟨observed,revealed,fun other right => right.functional revealed⟩

theorem worldTyped_initialized_reveals {program : Kernel.Program} {world : World} {address : Address}
    (typed : Typing.WorldTyped program world) (initialized : world.Initialized address) :
    ∃ value observed, world.Stores address value ∧ Reveals world value observed := by
  obtain ⟨value,stored,active⟩ := initialized
  obtain ⟨observed,revealed⟩ := valueTyped_reveals (typed.2.1 address value (World.resident_iff_stores.mpr stored)) active
  exact ⟨value,observed,stored,revealed⟩

theorem Finished.of_stopped {program : Kernel.Program} {function : Kernel.Function} {state : Execution.State}
    {context : Execution.Context} {address : Address} (typed : Typing.WorldTyped program state.world)
    (stopped : state.task = .stopped context address) (initialized : state.world.Initialized address) :
    ∃ result, Finished program function state result := by
  obtain ⟨value,observed,stored,revealed⟩ := worldTyped_initialized_reveals typed initialized
  exact ⟨.returned observed,Or.inl ⟨context,address,value,observed,stopped,stored,revealed,rfl⟩⟩

/-- An admitted outward request is a genuine final public observation, even
when a payload contains an operation value or captured/contextual residents. -/
theorem mayAwait_finished {program : Kernel.Program} {function : Kernel.Function} {state : Execution.State}
    (typed : Typing.WorldTyped program state.world) (awaiting : Contracts.MayAwait program function state) :
    ∃ result, Finished program function state result := by
  have admission := awaiting
  obtain ⟨context,id,arguments,payload,operation,signature,task,selected,row,inputs,outward,permission⟩ := awaiting
  have payloads : ∃ residents observations,
      ListRel (fun source value => state.world.Stores source.address value) payload residents ∧
        ListRel (Reveals state.world) residents observations := by
    clear task outward permission admission
    induction payload with
    | nil => exact ⟨[],[],.nil,.nil⟩
    | cons source rest ih =>
      obtain ⟨value,observed,stored,revealed⟩ := worldTyped_initialized_reveals typed (inputs source (by simp)).1
      obtain ⟨residents,observations,restStored,restRevealed⟩ := ih (fun entry member => inputs entry (by simp [member]))
      exact ⟨value :: residents,observed :: observations,.cons stored restStored,.cons revealed restRevealed⟩
  obtain ⟨residents,observations,stored,revealed⟩ := payloads
  exact ⟨.outward id arguments observations,Or.inr (Or.inr
    ⟨context,id,arguments,payload,residents,observations,task,admission,stored,revealed,rfl⟩)⟩

theorem finished_stopped_iff {program : Kernel.Program} {function : Kernel.Function} {state : Execution.State}
    {context : Execution.Context} {address : Address} (typed : Typing.WorldTyped program state.world)
    (stopped : state.task = .stopped context address) :
    (∃ result, Finished program function state result) ↔ state.world.Initialized address := by
  constructor
  · rintro ⟨result,finished⟩
    rcases finished with ⟨found,stoppedAt,value,observed,task,stored,revealed,_⟩ | ⟨reason,task,_⟩ |
      ⟨performing,id,arguments,payload,residents,observations,task,_⟩
    · obtain ⟨_,equal⟩ := Execution.Task.stopped.inj (task.symm.trans stopped)
      subst stoppedAt
      exact ⟨value,stored,revealed.initialized⟩
    · simp [stopped] at task
    · simp [stopped] at task
  · exact Finished.of_stopped typed stopped

end Specification

namespace Specification

/-- Exact remaining result-lifetime obligation after full storage preservation
and semantic resource progress. This is a characterization, not a claim that
the task/continuation invariant has already proved initialized returns. -/
theorem resourceAdmission_safe_iff {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {access : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (admitted : Contracts.ResourceAdmissionAt program function access)
    (inputAccess : ∀ input ∈ inputs, (∃ index, input.origin = .capture index) → input.access = access) :
    (Semantics program host function inputs).Safe ↔
      ∀ state, (Semantics program host function inputs).Reachable state →
        ∀ context address, state.task = .stopped context address → state.world.Initialized address := by
  constructor
  · intro safe state reachable context address stopped
    rcases (safe state reachable).2 with final | ⟨event,after,internal,step,_⟩
    · exact (finished_stopped_iff (reachable_worldTyped valid inventory lawful reachable) stopped).mp final
    · exact False.elim (step.not_stopped stopped)
  · intro results state reachable
    have typed := reachable_worldTyped valid inventory lawful reachable
    refine ⟨fun invalid => invalid typed,?_⟩
    obtain ⟨start,trace,initial,run⟩ := reachable_execution_iff.mp reachable
    have progress := (admitted host inputs .isolated start trace state lawful initial inputAccess
      (Contracts.invocation_isolated run)).1
    rcases progress with ⟨address,context,stopped⟩ | ⟨reason,fatal⟩ | awaiting | transfer | ⟨event,after,_,step⟩
    · exact Or.inl (Finished.of_stopped typed stopped (results state reachable context address stopped))
    · exact Or.inl ⟨.fatal reason,Or.inr (Or.inl ⟨reason,fatal,rfl⟩)⟩
    · exact Or.inl (mayAwait_finished typed awaiting)
    · exact False.elim (Contracts.MayTransfer.isolated_false transfer)
    · exact Or.inr ⟨event.bind publicEvent,after,event,step,rfl⟩

theorem WellFormed.safe_iff_initialized_returns {program : Kernel.Program} (well : WellFormed program)
    {host : Foreign.Model} {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {id : DeclId} {arguments : List Term}
    (lawful : host.Lawful program) (selected : Kernel.Instance program id arguments function)
    (inputAccess : ∀ input ∈ inputs, (∃ index, input.origin = .capture index) → input.access = .owned) :
    (Semantics program host function inputs).Safe ↔
      ∀ state, (Semantics program host function inputs).Reachable state →
        ∀ context address, state.task = .stopped context address → state.world.Initialized address :=
  resourceAdmission_safe_iff well.declarations well.inventory lawful
    (well.functions id arguments function selected).2.1 inputAccess

end Specification
end Glorious.Language
