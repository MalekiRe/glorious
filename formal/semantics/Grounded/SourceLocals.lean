import Grounded.Soundness

/-! Named local resolution feeds the existing decoded-core checking rules.
A scope owns source spellings and allocates lexical IDs; runtime execution never
consults spellings. This is local elaboration, not a parser or type inference. -/
namespace Grounded

structure SourceBinding where
  spelling : Option Identifier
  identity : BindingId
  slot : BindingType

structure SourceScope where
  bindings : List SourceBinding
  next : Nat
  distinct : (bindings.map SourceBinding.identity).Nodup
  below : ∀ binding ∈ bindings, binding.identity.index < next

def SourceScope.empty : SourceScope := ⟨[], 0, .nil, by simp⟩

def SourceScope.context (scope : SourceScope) : List (BindingId × BindingType) :=
  scope.bindings.map fun binding => (binding.identity, binding.slot)

/-- Nearest source spelling wins. An absent name is not an invented binding. -/
def SourceScope.resolve (scope : SourceScope) (spelling : Identifier) : Option SourceBinding :=
  scope.bindings.find? (fun binding => binding.spelling == some spelling)

theorem SourceScope.fresh (scope : SourceScope) :
    (⟨scope.next⟩ : BindingId) ∉ scope.bindings.map SourceBinding.identity := by
  intro member
  obtain ⟨binding, member, equal⟩ := List.mem_map.mp member
  have bound := scope.below binding member
  rw [equal] at bound
  exact Nat.lt_irrefl _ bound

/-- Named and hygienic anonymous bindings share one identity allocator. -/
def SourceScope.enter (scope : SourceScope) (spelling : Option Identifier) (slot : BindingType) : SourceScope where
  bindings := ⟨spelling, ⟨scope.next⟩, slot⟩ :: scope.bindings
  next := scope.next + 1
  distinct := List.nodup_cons.mpr ⟨scope.fresh, scope.distinct⟩
  below := by
    intro binding member
    cases member with
    | head => exact Nat.lt_succ_self _
    | tail _ member => exact Nat.lt_succ_of_lt (scope.below binding member)

theorem SourceScope.enter_resolve (scope : SourceScope) (spelling : Identifier) (slot : BindingType) :
    (scope.enter (some spelling) slot).resolve spelling = some ⟨some spelling, ⟨scope.next⟩, slot⟩ := by
  simp [resolve, enter]

theorem SourceScope.enter_resolve_other (scope : SourceScope) (spelling other : Identifier) (slot : BindingType)
    (different : spelling ≠ other) :
    (scope.enter (some spelling) slot).resolve other = scope.resolve other := by
  simp [resolve, enter, different]

/-- A compiler temporary cannot shadow any source name. -/
theorem SourceScope.enter_anonymous_resolve (scope : SourceScope) (slot : BindingType) (name : Identifier) :
    (scope.enter none slot).resolve name = scope.resolve name := by
  simp [resolve, enter]

private theorem selected_binding {bindings : List SourceBinding} {binding : SourceBinding}
    (distinct : (bindings.map SourceBinding.identity).Nodup) (member : binding ∈ bindings) :
    lookup binding.identity (bindings.map (fun entry => (entry.identity, entry.slot))) = some binding.slot := by
  induction bindings with
  | nil => cases member
  | cons head tail ih =>
    have parts := List.nodup_cons.mp distinct
    cases member with
    | head => simp [lookup]
    | tail _ member =>
      have different : binding.identity ≠ head.identity := by
        intro same
        exact parts.1 (same ▸ List.mem_map.mpr ⟨binding, member, rfl⟩)
      simp [lookup, different, ih parts.2 member]

theorem SourceScope.selected {scope : SourceScope} {spelling : Identifier} {binding : SourceBinding}
    (resolved : scope.resolve spelling = some binding) :
    lookup binding.identity scope.context = some binding.slot :=
  selected_binding scope.distinct (List.mem_of_find?_eq_some resolved)

/-- Successful resolution selects precisely the first matching spelling. -/
theorem SourceScope.resolve_first (scope : SourceScope) (spelling : Identifier) (binding : SourceBinding) :
    scope.resolve spelling = some binding ↔ binding.spelling = some spelling ∧
      ∃ before after, scope.bindings = before ++ binding :: after ∧
        ∀ earlier ∈ before, earlier.spelling ≠ some spelling := by
  simp [resolve, List.find?_eq_some_iff_append]

theorem SourceScope.resolve_missing (scope : SourceScope) (spelling : Identifier) :
    scope.resolve spelling = none ↔ ∀ binding ∈ scope.bindings, binding.spelling ≠ some spelling := by
  simp [resolve, List.find?_eq_none]

/-- Shadowing changes future name resolution, never an already-resolved outer
reference. This includes the case where both declarations have the same spelling. -/
theorem SourceScope.enter_preserves_selected {scope : SourceScope} {spelling : Identifier} {binding : SourceBinding}
    (resolved : scope.resolve spelling = some binding) (newName : Identifier) (slot : BindingType) :
    lookup binding.identity (scope.enter (some newName) slot).context = some binding.slot := by
  have different : binding.identity ≠ (⟨scope.next⟩ : BindingId) := by
    intro equal
    have bound := scope.below binding (List.mem_of_find?_eq_some resolved)
    rw [equal] at bound
    exact Nat.lt_irrefl _ bound
  change (if binding.identity = ⟨scope.next⟩ then some slot else lookup binding.identity scope.context) = some binding.slot
  rw [if_neg different]
  exact scope.selected resolved


/-- A write through the newly resolved binding cannot overwrite an outer root.
The compared environments are immediately before/after the destination write;
RHS effects have already happened and are not claimed to be undone. -/
theorem SourceScope.shadow_assignment_preserves_outer {scope : SourceScope} {spelling : Identifier}
    {binding : SourceBinding} (resolved : scope.resolve spelling = some binding)
    {program : Program} {fields outerFields : List FieldKey} {value : Value}
    {assignmentHome : Module} {before : Environment} {after : Configuration} {stack : List Frame} {rest : Expr}
    {context : FlowContext} (store : BindingMap.Typed program before.heap before.activation before.bindings context)
    (step : Step program ⟨before, .install assignmentHome ⟨⟨scope.next⟩, fields⟩ value rest, stack⟩ after) :
    after.environment.read program ⟨binding.identity, outerFields⟩ =
      before.read program ⟨binding.identity, outerFields⟩ := by
  apply Step.assignment_frame store.addresses_distinct step
  intro equal
  change binding.identity = (⟨scope.next⟩ : BindingId) at equal
  have member : binding.identity ∈ scope.bindings.map SourceBinding.identity :=
    List.mem_map.mpr ⟨binding, List.mem_of_find?_eq_some resolved, rfl⟩
  rw [equal] at member
  exact scope.fresh member


/-- Resolution produces the exact core place; projection authority remains the
shared PathType judgment, rather than a second source-field analysis. -/
def SourceScope.resolvePlace (scope : SourceScope) (spelling : Identifier) (fields : List FieldKey) : Option Place :=
  (scope.resolve spelling).map (fun binding => ⟨binding.identity, fields⟩)

variable {program : Program} {home : Module}

theorem SourceScope.place {scope : SourceScope} {spelling : Identifier} {fields : List FieldKey}
    {binding : SourceBinding} {type : Ty} (resolved : scope.resolve spelling = some binding)
    (path : PathType program home binding.slot.type fields type) :
    scope.resolvePlace spelling fields = some ⟨binding.identity, fields⟩ ∧
      PlaceType program home scope.context ⟨binding.identity, fields⟩ type binding.slot.mutable := by
  refine ⟨by simp [resolvePlace, resolved], ?_⟩
  exact .root (scope.selected resolved) path

theorem SourceScope.selected_slot {scope : SourceScope} {spelling : Identifier} {binding : SourceBinding}
    {context : FlowContext} {state : BindingState} (resolved : scope.resolve spelling = some binding)
    (slots : context.slots = scope.context) (selected : lookup binding.identity context = some state) :
    state.slot = binding.slot := by
  have found := scope.selected resolved
  rw [← slots, FlowContext.slots, lookup.map, selected] at found
  exact Option.some.inj found

theorem SourceScope.read_checked {scope : SourceScope} {spelling : Identifier} {fields : List FieldKey}
    {binding : SourceBinding} {type : Ty} {context : FlowContext} {state : BindingState} {available : Initialization}
    (resolved : scope.resolve spelling = some binding) (slots : context.slots = scope.context)
    (selected : lookup binding.identity context = some state)
    (path : PathType program home binding.slot.type fields type)
    (selection : state.initialization.selectFields program binding.slot.type fields = some available)
    (ready : available.Ready) (copyable : UsePermitted program.data .copy type) :
    HasType program home context (.read ⟨binding.identity, fields⟩) type context := by
  have same := scope.selected_slot resolved slots selected
  exact .read selected (by rw [same]; exact path) (by rw [same]; exact selection) ready copyable

theorem SourceScope.move_checked {scope : SourceScope} {spelling : Identifier} {fields : List FieldKey}
    {binding : SourceBinding} {type : Ty} {before after : FlowContext} {state : BindingState}
    {available updated : Initialization}
    (resolved : scope.resolve spelling = some binding) (slots : before.slots = scope.context)
    (selected : lookup binding.identity before = some state)
    (path : PathType program home binding.slot.type fields type)
    (selection : state.initialization.selectFields program binding.slot.type fields = some available)
    (ready : available.Ready)
    (mask : state.initialization.writeFields program binding.slot.type fields .absent = some updated)
    (context : replaceBinding binding.identity { state with initialization := updated } before = some after) :
    HasType program home before (.move ⟨binding.identity, fields⟩) type after := by
  have same := scope.selected_slot resolved slots selected
  exact .move selected (by rw [same]; exact path) (by rw [same]; exact selection) ready
    (by rw [same]; exact mask) context

/-- Destination selection uses the RHS output state, not the incoming state. -/
theorem SourceScope.assign_checked {scope : SourceScope} {spelling : Identifier} {fields : List FieldKey}
    {binding : SourceBinding} {actualType type result : Ty} {value rest : Expr}
    {before evaluated restored after : FlowContext} {state : BindingState} {updated available : Initialization}
    (resolved : scope.resolve spelling = some binding) (slots : before.slots = scope.context)
    (resident : HasType program home before value actualType evaluated)
    (joined : ReturnJoin program actualType evaluated type evaluated)
    (selected : lookup binding.identity evaluated = some state)
    (path : PathType program home binding.slot.type fields type) (writable : binding.slot.mutable = true)
    (selection : state.initialization.selectFields program binding.slot.type fields = some available)
    (discard : actualType ≠ .never → available.Disposable program.data type)
    (mask : state.initialization.writeFields program binding.slot.type fields .present = some updated)
    (context : replaceBinding binding.identity { state with initialization := updated } evaluated = some restored)
    (continued : HasType program home restored rest result after) :
    HasType program home before (.assign home ⟨binding.identity, fields⟩ value rest) (actualType.sequenceResult result) after := by
  have same := scope.selected_slot resolved (resident.slots.trans slots) selected
  exact .assign resident joined selected (by rw [same]; exact path) (by rw [same]; exact writable)
    (by rw [same]; exact selection) discard
    (by rw [same]; exact mask) context continued

theorem SourceScope.bind_checked (scope : SourceScope) (mutable : Bool)
    {initial body : Expr} {initialType localType result : Ty} {before middle after : FlowContext} {finalMask : Initialization}
    (slots : before.slots = scope.context)
    (initialized : HasType program home before initial initialType middle)
    (joined : ReturnJoin program initialType middle localType middle)
    (discard : initialType ≠ .never → ReturnDisposition program result [(⟨scope.next⟩, ⟨⟨localType, mutable⟩, finalMask⟩)])
    (continued : HasType program home ((⟨scope.next⟩, ⟨⟨localType, mutable⟩, .present⟩) :: middle) body result
      ((⟨scope.next⟩, ⟨⟨localType, mutable⟩, finalMask⟩) :: after)) :
    HasType program home before (.bind mutable ⟨scope.next⟩ localType initial body) result after := by
  refine .bind initialized joined discard continued ?_
  have keys := congrArg (List.map Prod.fst) (initialized.slots.trans slots)
  simp only [FlowContext.slots, SourceScope.context, List.map_map, Function.comp_def] at keys
  rw [keys]
  exact scope.fresh



end Grounded
