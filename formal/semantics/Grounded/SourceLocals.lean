import Grounded.Soundness

/-! Named local resolution feeds the existing decoded-core checking rules.
A scope owns source spellings and allocates lexical IDs; runtime execution never
consults spellings. This is local elaboration, not a parser or type inference. -/
namespace Grounded

structure SourceBinding where
  spelling : String
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
def SourceScope.resolve (scope : SourceScope) (spelling : String) : Option SourceBinding :=
  scope.bindings.find? (fun binding => binding.spelling == spelling)

theorem SourceScope.fresh (scope : SourceScope) :
    (⟨scope.next⟩ : BindingId) ∉ scope.bindings.map SourceBinding.identity := by
  intro member
  obtain ⟨binding, member, equal⟩ := List.mem_map.mp member
  have bound := scope.below binding member
  rw [equal] at bound
  exact Nat.lt_irrefl _ bound

/-- The binder is installed only for its body, not its initializer. -/
def SourceScope.enter (scope : SourceScope) (spelling : String) (slot : BindingType) : SourceScope where
  bindings := ⟨spelling, ⟨scope.next⟩, slot⟩ :: scope.bindings
  next := scope.next + 1
  distinct := List.nodup_cons.mpr ⟨scope.fresh, scope.distinct⟩
  below := by
    intro binding member
    cases member with
    | head => exact Nat.lt_succ_self _
    | tail _ member => exact Nat.lt_succ_of_lt (scope.below binding member)

theorem SourceScope.enter_resolve (scope : SourceScope) (spelling : String) (slot : BindingType) :
    (scope.enter spelling slot).resolve spelling = some ⟨spelling, ⟨scope.next⟩, slot⟩ := by
  simp [resolve, enter]

theorem SourceScope.enter_resolve_other (scope : SourceScope) (spelling other : String) (slot : BindingType)
    (different : spelling ≠ other) :
    (scope.enter spelling slot).resolve other = scope.resolve other := by
  simp [resolve, enter, different]

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

theorem SourceScope.selected {scope : SourceScope} {spelling : String} {binding : SourceBinding}
    (resolved : scope.resolve spelling = some binding) :
    lookup binding.identity scope.context = some binding.slot :=
  selected_binding scope.distinct (List.mem_of_find?_eq_some resolved)

/-- Successful resolution selects precisely the first matching spelling. -/
theorem SourceScope.resolve_first (scope : SourceScope) (spelling : String) (binding : SourceBinding) :
    scope.resolve spelling = some binding ↔ binding.spelling = spelling ∧
      ∃ before after, scope.bindings = before ++ binding :: after ∧
        ∀ earlier ∈ before, earlier.spelling ≠ spelling := by
  simp [resolve, List.find?_eq_some_iff_append]

theorem SourceScope.resolve_missing (scope : SourceScope) (spelling : String) :
    scope.resolve spelling = none ↔ ∀ binding ∈ scope.bindings, binding.spelling ≠ spelling := by
  simp [resolve, List.find?_eq_none]

/-- Shadowing changes future name resolution, never an already-resolved outer
reference. This includes the case where both declarations have the same spelling. -/
theorem SourceScope.enter_preserves_selected {scope : SourceScope} {spelling : String} {binding : SourceBinding}
    (resolved : scope.resolve spelling = some binding) (newName : String) (slot : BindingType) :
    lookup binding.identity (scope.enter newName slot).context = some binding.slot := by
  have different : binding.identity ≠ (⟨scope.next⟩ : BindingId) := by
    intro equal
    have bound := scope.below binding (List.mem_of_find?_eq_some resolved)
    rw [equal] at bound
    exact Nat.lt_irrefl _ bound
  change (if binding.identity = ⟨scope.next⟩ then some slot else lookup binding.identity scope.context) = some binding.slot
  rw [if_neg different]
  exact scope.selected resolved


/-- Resolution produces the exact core place; projection authority remains the
shared PathType judgment, rather than a second source-field analysis. -/
def SourceScope.resolvePlace (scope : SourceScope) (spelling : String) (fields : List FieldKey) : Option Place :=
  (scope.resolve spelling).map (fun binding => ⟨binding.identity, fields⟩)

variable {program : Program} {home : Module}

theorem SourceScope.place {scope : SourceScope} {spelling : String} {fields : List FieldKey}
    {binding : SourceBinding} {type : Ty} (resolved : scope.resolve spelling = some binding)
    (path : PathType program home binding.slot.type fields type) :
    scope.resolvePlace spelling fields = some ⟨binding.identity, fields⟩ ∧
      PlaceType program home scope.context ⟨binding.identity, fields⟩ type binding.slot.mutable := by
  refine ⟨by simp [resolvePlace, resolved], ?_⟩
  exact .root (scope.selected resolved) path

theorem SourceScope.read_checked {scope : SourceScope} {spelling : String} {fields : List FieldKey}
    {binding : SourceBinding} {type : Ty} (resolved : scope.resolve spelling = some binding)
    (path : PathType program home binding.slot.type fields type) (copyable : Duplicable program.data type) :
    HasType program home scope.context (.read ⟨binding.identity, fields⟩) type :=
  .read (scope.place resolved path).2 copyable

theorem SourceScope.assign_checked {scope : SourceScope} {spelling : String} {fields : List FieldKey}
    {binding : SourceBinding} {type result : Ty} {value rest : Expr}
    (resolved : scope.resolve spelling = some binding)
    (path : PathType program home binding.slot.type fields type) (writable : binding.slot.mutable = true)
    (discard : Duplicable program.data type) (resident : HasType program home scope.context value type)
    (continued : HasType program home scope.context rest result) :
    HasType program home scope.context (.assign ⟨binding.identity, fields⟩ value rest) result := by
  have place := (scope.place resolved path).2
  rw [writable] at place
  exact .assign place discard resident continued

theorem SourceScope.bind_checked (scope : SourceScope) (spelling : String) (mutable : Bool)
    {annotation : Option TypeExpr} {initial body : Expr} {localType result : Ty}
    (initialized : HasType program home scope.context initial localType)
    (discard : Duplicable program.data localType) (annotated : Annotation program.aliases annotation localType)
    (continued : HasType program home (scope.enter spelling ⟨localType, mutable⟩).context body result) :
    HasType program home scope.context (.bind mutable ⟨scope.next⟩ annotation initial body) result := by
  refine .bind initialized discard annotated continued ?_
  simpa [context, List.map_map, Function.comp_def] using scope.fresh

/-- Actual named-local elaboration constructs core admission and then consumes
ordinary machine soundness. No completed execution or successor readiness is supplied. -/
theorem SourceScope.bind_soundness (checkedProgram : program.Checked)
    (scope : SourceScope) (spelling : String) (mutable : Bool)
    {annotation : Option TypeExpr} {initial body : Expr} {localType result : Ty}
    (initialized : HasType program home scope.context initial localType)
    (discard : Duplicable program.data localType) (annotated : Annotation program.aliases annotation localType)
    (continued : HasType program home (scope.enter spelling ⟨localType, mutable⟩).context body result)
    {environment : Environment} (store : EnvironmentTyped program environment scope.context) {state : Configuration}
    (run : Run program ⟨environment, .expression (.bind mutable ⟨scope.next⟩ annotation initial body), []⟩ state) :
    ConfigurationTyped program scope.context (.one result) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      EnvironmentFrame scope.context environment state.outerEnvironment ∧
      (state.environment.map Prod.fst).Nodup :=
  (scope.bind_checked spelling mutable initialized discard annotated continued).soundness checkedProgram store run

theorem SourceScope.read_soundness (checkedProgram : program.Checked)
    {scope : SourceScope} {spelling : String} {fields : List FieldKey} {binding : SourceBinding} {type : Ty}
    (resolved : scope.resolve spelling = some binding)
    (path : PathType program home binding.slot.type fields type) (copyable : Duplicable program.data type)
    {environment : Environment} (store : EnvironmentTyped program environment scope.context) {state : Configuration}
    (run : Run program ⟨environment, .expression (.read ⟨binding.identity, fields⟩), []⟩ state) :
    ConfigurationTyped program scope.context (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      EnvironmentFrame scope.context environment state.outerEnvironment ∧
      (state.environment.map Prod.fst).Nodup :=
  (scope.read_checked resolved path copyable).soundness checkedProgram store run

theorem SourceScope.assign_soundness (checkedProgram : program.Checked)
    {scope : SourceScope} {spelling : String} {fields : List FieldKey} {binding : SourceBinding}
    {type result : Ty} {value rest : Expr} (resolved : scope.resolve spelling = some binding)
    (path : PathType program home binding.slot.type fields type) (writable : binding.slot.mutable = true)
    (discard : Duplicable program.data type) (resident : HasType program home scope.context value type)
    (continued : HasType program home scope.context rest result)
    {environment : Environment} (store : EnvironmentTyped program environment scope.context) {state : Configuration}
    (run : Run program ⟨environment, .expression (.assign ⟨binding.identity, fields⟩ value rest), []⟩ state) :
    ConfigurationTyped program scope.context (.one result) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      EnvironmentFrame scope.context environment state.outerEnvironment ∧
      (state.environment.map Prod.fst).Nodup :=
  (scope.assign_checked resolved path writable discard resident continued).soundness checkedProgram store run


end Grounded
