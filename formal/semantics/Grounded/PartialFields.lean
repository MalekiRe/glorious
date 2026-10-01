import Grounded.PartialStorage
import Grounded.Projections

/-! Declared layout opens live holes for field restoration without inventing
resident values. Projection authority remains the shared ProjectionType. -/
namespace Grounded

def Ty.fieldTypes (program : Program) : Ty → Option (List Ty)
  | .tuple first rest => some (first :: rest)
  | .nominal identity => (program.data identity).bind fun declaration =>
      (declaration.constructor none).map fun schema => schema.residents.map Field.type
  | _ => none


def Initialization.openFields (state : Initialization) (count : Nat) : List Initialization :=
  match state with
  | .absent => List.replicate count .absent
  | .present => List.replicate count .present
  | .fields states => states

def PartialValue.openFields (program : Program) (type : Ty) (value : PartialValue) :
    Option (List PartialValue) :=
  match type, value with
  | .tuple _ rest, .hole => some (List.replicate (rest.length + 1) .hole)
  | .nominal identity, .hole => (program.data identity).bind fun declaration =>
      (declaration.constructor none).map fun schema => List.replicate schema.residents.length .hole
  | .tuple _ _, .resident (.tuple head tail) => some ((head :: tail).map .resident)
  | .nominal identity, .resident (.nominal other none fields) =>
      if identity = other then some (fields.map .resident) else none
  | .tuple _ _, .tuple head tail => some (head :: tail)
  | .nominal identity, .nominal other none fields =>
      if identity = other then some fields else none
  | _, _ => none

def PartialValue.closeFields (type : Ty) (fields : List PartialValue) : Option PartialValue :=
  match type, fields with
  | .tuple _ _, head :: tail => some (.tuple head tail)
  | .nominal identity, fields => some (.nominal identity none fields)
  | _, _ => none

theorem PartialValuesTyped.length {program : Program} {values : List PartialValue}
    {types : List Ty} {states : List Initialization}
    (typed : PartialValuesTyped program values types states) :
    values.length = types.length ∧ states.length = types.length := by
  induction types generalizing values states with
  | nil => cases typed; exact ⟨rfl, rfl⟩
  | cons type types ih =>
    cases typed with
    | cons head tail =>
      obtain ⟨values, states⟩ := ih tail
      exact ⟨congrArg Nat.succ values, congrArg Nat.succ states⟩

theorem PartialValuesTyped.holes (program : Program) (types : List Ty) :
    PartialValuesTyped program (List.replicate types.length .hole) types
      (List.replicate types.length .absent) := by
  induction types with
  | nil => exact .nil
  | cons type types ih => exact .cons (.hole type) ih

theorem ValuesHaveTypes.partialResidents {program : Program} {values : List Value} {types : List Ty}
    (typed : ValuesHaveTypes program values types) :
    PartialValuesTyped program (values.map PartialValue.resident) types
      (List.replicate types.length .present) := by
  induction types generalizing values with
  | nil => cases typed; exact .nil
  | cons type types ih =>
    cases typed with
    | cons head tail => exact .cons (.resident head) (ih tail)

theorem PartialValuesTyped.select {program : Program} {values : List PartialValue}
    {types : List Ty} {states : List Initialization}
    (typed : PartialValuesTyped program values types states) {index : Nat} {type : Ty}
    (selected : types[index]? = some type) :
    ∃ value state, values[index]? = some value ∧ states[index]? = some state ∧
      value.Typed program type state := by
  induction types generalizing values states index with
  | nil => simp at selected
  | cons first rest ih =>
    cases typed with
    | cons head tail =>
      cases index with
      | zero => cases selected; exact ⟨_, _, rfl, rfl, head⟩
      | succ index => exact ih tail selected

theorem PartialValuesTyped.set {program : Program} {values : List PartialValue}
    {types : List Ty} {states : List Initialization}
    (typed : PartialValuesTyped program values types states) {index : Nat} {type : Ty}
    (selected : types[index]? = some type) {value : PartialValue} {state : Initialization}
    (replacement : value.Typed program type state) :
    PartialValuesTyped program (values.set index value) types (states.set index state) := by
  induction types generalizing values states index with
  | nil => simp at selected
  | cons first rest ih =>
    cases typed with
    | cons head tail =>
      cases index with
      | zero => cases selected; exact .cons replacement tail
      | succ index => exact .cons head (ih tail selected)

/-- Opening derives the actual field list and its initialization states from
the same checked projection. It works for absent, whole, and partial owners. -/
theorem ProjectionType.open_partial {program : Program} {home : Module} {parent child : Ty}
    {key : FieldKey} {index : Nat} (projection : ProjectionType program home parent key index child)
    {value : PartialValue} {state : Initialization} (typed : value.Typed program parent state) :
    ∃ types, parent.fieldTypes program = some types ∧
      ∃ fields, types[index]? = some child ∧ value.openFields program parent = some fields ∧
        PartialValuesTyped program fields types (state.openFields types.length) := by
  cases projection with
  | @tuple first rest index child selected =>
    refine ⟨first :: rest, rfl, ?_⟩
    cases typed with
    | hole => exact ⟨_, selected, rfl, PartialValuesTyped.holes program (first :: rest)⟩
    | resident resident =>
      cases resident with
      | tuple head tail => exact ⟨_, selected, rfl, (ValuesHaveTypes.cons head tail).partialResidents⟩
    | tuple head tail => exact ⟨_, selected, rfl, .cons head tail⟩
  | @nominal identity index declaration schema field key declared structureOnly indexed selected visible =>
    have chosen : declaration.constructor none = some schema := by
      simp [DataDecl.constructor, structureOnly]
    have child : (schema.residents.map Field.type)[index]? = some field.type := by
      simp [List.getElem?_map, selected]
    refine ⟨schema.residents.map Field.type, by simp [Ty.fieldTypes, declared, chosen], ?_⟩
    cases typed with
    | hole =>
      refine ⟨List.replicate schema.residents.length .hole, child, ?_, ?_⟩
      · simp [PartialValue.openFields, declared, chosen]
      · simpa only [List.length_map, Initialization.openFields] using
          PartialValuesTyped.holes program (schema.residents.map Field.type)
    | resident resident =>
      cases resident with
      | @nominal _ tag otherDeclaration otherSchema values otherDeclared otherChosen finite residents =>
        have same := Option.some.inj (otherDeclared.symm.trans declared)
        subst otherDeclaration
        cases tag with
        | some tag => simp [DataDecl.constructor, structureOnly] at otherChosen
        | none =>
          have sameSchema := Option.some.inj (otherChosen.symm.trans chosen)
          subst otherSchema
          exact ⟨_, child, by simp [PartialValue.openFields], residents.partialResidents⟩
    | @nominal _ tag otherDeclaration otherSchema fields states otherDeclared otherChosen finite residents =>
      have same := Option.some.inj (otherDeclared.symm.trans declared)
      subst otherDeclaration
      cases tag with
      | some tag => simp [DataDecl.constructor, structureOnly] at otherChosen
      | none =>
        have sameSchema := Option.some.inj (otherChosen.symm.trans chosen)
        subst otherSchema
        exact ⟨_, child, by simp [PartialValue.openFields], residents⟩


theorem PartialValuesTyped.close {program : Program} {parent : Ty} {types : List Ty}
    {fields : List PartialValue} {states : List Initialization}
    (layout : parent.fieldTypes program = some types)
    (finite : FiniteLayout program.target program.data parent)
    (typed : PartialValuesTyped program fields types states) :
    ∃ value, PartialValue.closeFields parent fields = some value ∧
      value.Typed program parent (.fields states) ∧
      value.openFields program parent = some fields := by
  cases parent with
  | tuple first rest =>
    simp only [Ty.fieldTypes, Option.some.injEq] at layout
    subst types
    cases typed with
    | cons head tail => exact ⟨_, rfl, .tuple head tail, rfl⟩
  | nominal identity =>
    simp only [Ty.fieldTypes, Option.bind_eq_some_iff, Option.map_eq_some_iff] at layout
    obtain ⟨declaration, declared, schema, chosen, same⟩ := layout
    subst types
    exact ⟨_, rfl, .nominal declared chosen finite typed, by simp [PartialValue.openFields]⟩
  | _ => simp [Ty.fieldTypes] at layout

/-- The index is the resolved index supplied by the shared projection contract.
Opening an absent parent creates only holes, never fabricated old residents. -/
def PartialValue.replaceField (program : Program) (parent : Ty) (value : PartialValue)
    (index : Nat) (replacement : PartialValue) : Option PartialValue :=
  (value.openFields program parent).bind fun fields =>
    fields[index]?.bind fun _ => closeFields parent (fields.set index replacement)

theorem ProjectionType.replace_partial {program : Program} {home : Module} {parent child : Ty}
    {key : FieldKey} {index : Nat} (projection : ProjectionType program home parent key index child)
    {value replacement : PartialValue} {state replacementState : Initialization}
    (finite : FiniteLayout program.target program.data parent)
    (typed : value.Typed program parent state) (replacementTyped : replacement.Typed program child replacementState) :
    ∃ types fields after, parent.fieldTypes program = some types ∧
      value.openFields program parent = some fields ∧
      value.replaceField program parent index replacement = some after ∧
      after.Typed program parent (.fields ((state.openFields types.length).set index replacementState)) ∧
      after.openFields program parent = some (fields.set index replacement) ∧
      (fields.set index replacement)[index]? = some replacement := by
  obtain ⟨types, layout, fields, selected, opened, residents⟩ := projection.open_partial typed
  obtain ⟨old, oldState, found, _, _⟩ := residents.select selected
  obtain ⟨after, closed, afterTyped, reopened⟩ :=
    (residents.set selected replacementTyped).close layout finite
  exact ⟨types, fields, after, layout, opened,
    by simp [PartialValue.replaceField, opened, found, closed], afterTyped, reopened,
    List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1⟩

/-- Fields not selected by the actual replacement retain their partial
resident exactly, including holes and partially initialized subaggregates. -/
theorem PartialValue.replaceField_siblings {program : Program} {parent : Ty}
    {before after replacement : PartialValue} {index other : Nat} {fields : List PartialValue}
    (opened : before.openFields program parent = some fields)
    (written : before.replaceField program parent index replacement = some after)
    (different : index ≠ other) :
    ∃ afterFields, after.openFields program parent = some afterFields ∧
      afterFields[other]? = fields[other]? := by
  simp only [PartialValue.replaceField, opened, Option.bind_some] at written
  cases found : fields[index]? with
  | none => simp [found] at written
  | some old =>
    simp only [found, Option.bind_some] at written
    cases parent with
    | tuple first rest =>
      cases shape : fields.set index replacement with
      | nil => simp [PartialValue.closeFields, shape] at written
      | cons head tail =>
        simp only [PartialValue.closeFields, shape, Option.some.injEq] at written
        subst after
        refine ⟨head :: tail, rfl, ?_⟩
        rw [← shape]
        simp [different]
    | nominal identity =>
      simp only [PartialValue.closeFields, Option.some.injEq] at written
      subst after
      exact ⟨fields.set index replacement, by simp [PartialValue.openFields], by simp [different]⟩
    | _ => simp [PartialValue.closeFields] at written



theorem ProjectionType.finite_child {program : Program} {home : Module} {parent child : Ty}
    {key : FieldKey} {index : Nat} (projection : ProjectionType program home parent key index child)
    (finite : FiniteLayout program.target program.data parent) :
    FiniteLayout program.target program.data child := by
  cases projection with
  | tuple selected =>
    cases finite with
    | tuple first rest =>
      have member := List.mem_of_getElem? selected
      cases member with
      | head => exact first
      | tail _ member => exact rest _ member
  | nominal declared shape indexed selected visible =>
    cases finite with
    | nominal otherDeclared schemas fields =>
      have same := Option.some.inj (otherDeclared.symm.trans declared)
      subst_vars
      exact fields _ (by simp [DataDecl.schemas, shape]) _ (List.mem_of_getElem? selected)

def Ty.fieldIndex (program : Program) (parent : Ty) (key : FieldKey) : Option Nat :=
  match parent, key with
  | .tuple _ _, .positional index => some index
  | .nominal identity, key => (program.data identity).bind fun declaration =>
      (declaration.constructor none).bind fun schema => schema.index key
  | _, _ => none

def Ty.fieldInfo (program : Program) (parent : Ty) (key : FieldKey) : Option (Nat × Ty × List Ty) :=
  (parent.fieldTypes program).bind fun types =>
    (parent.fieldIndex program key).bind fun index =>
      types[index]?.map fun child => (index, child, types)

theorem ProjectionType.fieldIndex {program : Program} {home : Module} {parent child : Ty}
    {key : FieldKey} {index : Nat} (projection : ProjectionType program home parent key index child) :
    parent.fieldIndex program key = some index := by
  cases projection with
  | tuple selected => rfl
  | nominal declared shape indexed selected visible =>
    simp [Ty.fieldIndex, declared, DataDecl.constructor, shape, indexed]

theorem ProjectionType.fieldInfo {program : Program} {home : Module} {parent child : Ty}
    {key : FieldKey} {index : Nat} (projection : ProjectionType program home parent key index child)
    {types : List Ty} (layout : parent.fieldTypes program = some types)
    (selected : types[index]? = some child) :
    parent.fieldInfo program key = some (index, child, types) := by
  simp [Ty.fieldInfo, layout, projection.fieldIndex, selected]

def Initialization.writeFields (program : Program) (parent : Ty) (state : Initialization)
    (path : List FieldKey) (replacement : Initialization) : Option Initialization :=
  match path with
  | [] => some replacement
  | key :: rest => (parent.fieldInfo program key).bind fun (index, child, types) =>
      let states := state.openFields types.length
      states[index]?.bind fun current =>
        (current.writeFields program child rest replacement).map fun updated =>
          .fields (states.set index updated)

def PartialValue.writeFields (program : Program) (parent : Ty) (value : PartialValue)
    (path : List FieldKey) (replacement : PartialValue) : Option PartialValue :=
  match path with
  | [] => some replacement
  | key :: rest => (parent.fieldInfo program key).bind fun (index, child, _) =>
      (value.openFields program parent).bind fun fields =>
        fields[index]?.bind fun current =>
          (current.writeFields program child rest replacement).bind fun updated =>
            closeFields parent (fields.set index updated)

def PartialValue.selectFields (program : Program) (parent : Ty) (value : PartialValue)
    (path : List FieldKey) : Option PartialValue :=
  match path with
  | [] => some value
  | key :: rest => (parent.fieldInfo program key).bind fun (index, child, _) =>
      (value.openFields program parent).bind fun fields =>
        fields[index]?.bind fun current => current.selectFields program child rest

/-- A checked arbitrary-depth field path constructs both its static
initialization update and actual storage update, including through whole holes.
No successful write or post-state typing is an admission premise. -/
theorem PathType.restore_partial {program : Program} {home : Module} {parent child : Ty}
    {path : List FieldKey} (checked : PathType program home parent path child)
    {before replacement : PartialValue} {beforeState replacementState : Initialization}
    (finite : FiniteLayout program.target program.data parent)
    (typed : before.Typed program parent beforeState)
    (replacementTyped : replacement.Typed program child replacementState) :
    ∃ after afterState, beforeState.writeFields program parent path replacementState = some afterState ∧
      before.writeFields program parent path replacement = some after ∧
      after.Typed program parent afterState ∧
      after.selectFields program parent path = some replacement := by
  induction checked generalizing before beforeState with
  | here type => exact ⟨replacement, replacementState, rfl, rfl, replacementTyped, rfl⟩
  | @step parent middle child key index rest projection path ih =>
    obtain ⟨types, layout, fields, selected, opened, fieldsTyped⟩ := projection.open_partial typed
    obtain ⟨resident, state, found, stateFound, residentTyped⟩ := fieldsTyped.select selected
    obtain ⟨updated, updatedState, stateWritten, written, updatedTyped, readback⟩ :=
      ih (projection.finite_child finite) residentTyped replacementTyped
    obtain ⟨after, closed, afterTyped, reopened⟩ :=
      (fieldsTyped.set selected updatedTyped).close layout finite
    have info := projection.fieldInfo layout selected
    have readUpdated := List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1 (a := updated)
    exact ⟨after, .fields ((beforeState.openFields types.length).set index updatedState),
      by simp [Initialization.writeFields, info, stateFound, stateWritten],
      by simp [PartialValue.writeFields, info, opened, found, written, closed], afterTyped,
      by simp [PartialValue.selectFields, info, reopened, readUpdated, readback]⟩



def Initialization.selectFields (program : Program) (parent : Ty) (state : Initialization)
    (path : List FieldKey) : Option Initialization :=
  match path with
  | [] => some state
  | key :: rest => (parent.fieldInfo program key).bind fun (index, child, types) =>
      (state.openFields types.length)[index]?.bind fun current =>
        current.selectFields program child rest

theorem PathType.select_partial {program : Program} {home : Module} {parent child : Ty}
    {path : List FieldKey} (checked : PathType program home parent path child)
    {before : PartialValue} {beforeState : Initialization}
    (typed : before.Typed program parent beforeState) :
    ∃ selected selectedState, beforeState.selectFields program parent path = some selectedState ∧
      before.selectFields program parent path = some selected ∧
      selected.Typed program child selectedState := by
  induction checked generalizing before beforeState with
  | here type => exact ⟨before, beforeState, rfl, rfl, typed⟩
  | step projection path ih =>
    obtain ⟨types, layout, fields, selected, opened, fieldsTyped⟩ := projection.open_partial typed
    obtain ⟨resident, state, found, stateFound, residentTyped⟩ := fieldsTyped.select selected
    obtain ⟨selectedResident, selectedState, staticSelected, dynamicSelected, selectedTyped⟩ := ih residentTyped
    have info := projection.fieldInfo layout selected
    exact ⟨selectedResident, selectedState,
      by simp [Initialization.selectFields, info, stateFound, staticSelected],
      by simp [PartialValue.selectFields, info, opened, found, dynamicSelected], selectedTyped⟩



/-- Static restoration reestablishes the selected path's exact availability;
this is an algebraic property of the checking transformation, not a runtime
readiness assumption. -/
theorem Initialization.write_select {program : Program} {parent : Ty}
    {before after replacement : Initialization} {path : List FieldKey}
    (written : before.writeFields program parent path replacement = some after) :
    after.selectFields program parent path = some replacement := by
  induction path generalizing parent before after with
  | nil => cases written; rfl
  | cons key rest ih =>
    simp only [Initialization.writeFields, Option.bind_eq_some_iff, Option.map_eq_some_iff] at written
    obtain ⟨⟨index, child, types⟩, info, current, found, updated, tail, same⟩ := written
    subst after
    have atIndex := List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1 (a := updated)
    simp only [Initialization.selectFields, info, Option.bind_some]
    change (((before.openFields types.length).set index updated)[index]?).bind
      (fun current => current.selectFields program child rest) = some replacement
    rw [atIndex]
    exact ih tail


theorem InitializationsReady.replicate_present (count : Nat) :
    InitializationsReady (List.replicate count .present) := by
  induction count with
  | zero => exact .nil
  | succ count ih => exact .cons .present ih

theorem Initialization.Ready.openFields {state : Initialization} (ready : state.Ready) (count : Nat) :
    InitializationsReady (state.openFields count) := by
  cases ready with
  | present => exact InitializationsReady.replicate_present count
  | fields residents => exact residents

theorem InitializationsReady.select {states : List Initialization} (ready : InitializationsReady states)
    {index : Nat} {state : Initialization} (selected : states[index]? = some state) : state.Ready := by
  induction states generalizing index with
  | nil => simp at selected
  | cons first rest ih =>
    cases ready with
    | cons head tail =>
      cases index with
      | zero => cases selected; exact head
      | succ index => exact ih tail selected

theorem InitializationsReady.set {states : List Initialization} (ready : InitializationsReady states)
    (index : Nat) {state : Initialization} (replacement : state.Ready) :
    InitializationsReady (states.set index state) := by
  induction states generalizing index with
  | nil => exact .nil
  | cons first rest ih =>
    cases ready with
    | cons head tail =>
      cases index with
      | zero => exact .cons replacement tail
      | succ index => exact .cons head (ih tail index)

/-- Replacing a ready path with a ready resident cannot invalidate any other
path of an already initialized owner. -/
theorem Initialization.write_ready {program : Program} {parent : Ty}
    {before after replacement : Initialization} {path : List FieldKey}
    (ready : before.Ready) (replacementReady : replacement.Ready)
    (written : before.writeFields program parent path replacement = some after) : after.Ready := by
  induction path generalizing parent before after with
  | nil => cases written; exact replacementReady
  | cons key rest ih =>
    simp only [Initialization.writeFields, Option.bind_eq_some_iff, Option.map_eq_some_iff] at written
    obtain ⟨⟨index, child, types⟩, info, current, found, updated, tail, same⟩ := written
    subst after
    have fields := ready.openFields types.length
    exact .fields (fields.set index (ih (fields.select found) tail))


theorem Initialization.select_ready {program : Program} {parent : Ty}
    {before selectedState : Initialization} {path : List FieldKey}
    (ready : before.Ready)
    (selected : before.selectFields program parent path = some selectedState) : selectedState.Ready := by
  induction path generalizing parent before with
  | nil => cases selected; exact ready
  | cons key rest ih =>
    simp only [Initialization.selectFields, Option.bind_eq_some_iff] at selected
    obtain ⟨⟨index, child, types⟩, _, current, found, selected⟩ := selected
    exact ih ((ready.openFields types.length).select found) selected

end Grounded
