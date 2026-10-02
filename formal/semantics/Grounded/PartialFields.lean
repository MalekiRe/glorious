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
  | .maybe => List.replicate count .maybe
  | .fields states => states

theorem Initialization.Empty.open_field {before after : Initialization} {count index : Nat}
    (empty : before.Empty) (selected : (before.openFields count)[index]? = some after) : after.Empty := by
  have member := List.mem_of_getElem? selected
  cases before with
  | absent =>
    have same : after = .absent := (List.mem_replicate.mp member).2
    subst after
    trivial
  | present | maybe => simp [Initialization.Empty] at empty
  | fields states =>
    simp only [Initialization.Empty] at empty
    exact empty.2 after member


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

theorem PartialValue.closeFields_open {program : Program} {parent : Ty}
    {fields : List PartialValue} {after : PartialValue}
    (closed : PartialValue.closeFields parent fields = some after) :
    after.openFields program parent = some fields := by
  cases parent <;> cases fields <;> simp [PartialValue.closeFields] at closed
  all_goals subst after; simp [PartialValue.openFields]


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

theorem PartialValuesTyped.uncertain {program : Program} {values : List PartialValue}
    {types : List Ty} {states : List Initialization} (typed : PartialValuesTyped program values types states) :
    PartialValuesTyped program values types (List.replicate types.length .maybe) := by
  induction types generalizing values states with
  | nil => cases typed; exact .nil
  | cons first rest ih =>
    cases typed with
    | cons head tail => exact .cons (.uncertain head) (ih tail)


/-- Opening derives the actual field list and its initialization states from
the same checked projection. It works for absent, whole, and partial owners. -/
private theorem ProjectionType.open_partial_known {program : Program} {home : Module} {parent child : Ty}
    {key : FieldKey} {index : Nat} (projection : ProjectionType program home parent key index child)
    {value : PartialValue} {state : Initialization} (typed : value.Typed program parent state)
    (certain : state ≠ .maybe) :
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
    | uncertain => exact False.elim (certain rfl)
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
    | uncertain => exact False.elim (certain rfl)

/-- Projection preserves uncertainty; it never upgrades possible occupancy to
readiness. The runtime field list comes from the same checked projection. -/
theorem ProjectionType.open_partial {program : Program} {home : Module} {parent child : Ty}
    {key : FieldKey} {index : Nat} (projection : ProjectionType program home parent key index child)
    {value : PartialValue} {state : Initialization} (typed : value.Typed program parent state) :
    ∃ types, parent.fieldTypes program = some types ∧
      ∃ fields, types[index]? = some child ∧ value.openFields program parent = some fields ∧
        PartialValuesTyped program fields types (state.openFields types.length) := by
  induction typed using PartialValue.Typed.rec
    (motive_2 := fun _ _ _ _ => True) generalizing child key index with
  | hole => exact projection.open_partial_known (.hole _) (by intro same; cases same)
  | resident resident => exact projection.open_partial_known (.resident resident) (by intro same; cases same)
  | tuple head tail headIH tailIH =>
    exact projection.open_partial_known (.tuple head tail) (by intro same; cases same)
  | nominal declared chosen finite residents ih =>
    exact projection.open_partial_known (.nominal declared chosen finite residents) (by intro same; cases same)
  | uncertain typed ih =>
    obtain ⟨types, layout, fields, member, opened, residents⟩ := ih projection
    exact ⟨types, layout, fields, member, opened, residents.uncertain⟩
  | nil | cons => trivial



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

theorem Ty.fieldInfo_layout {program : Program} {parent child : Ty} {key : FieldKey}
    {index : Nat} {types : List Ty}
    (info : parent.fieldInfo program key = some (index, child, types)) :
    parent.fieldTypes program = some types := by
  simp only [Ty.fieldInfo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at info
  obtain ⟨actual, layout, position, indexed, selected, found, same⟩ := info
  cases same
  exact layout

theorem Ty.fieldInfo_child_unique {program : Program} {parent child other : Ty}
    {first second : FieldKey} {index : Nat} {types others : List Ty}
    (left : parent.fieldInfo program first = some (index, child, types))
    (right : parent.fieldInfo program second = some (index, other, others)) : child = other := by
  simp only [Ty.fieldInfo, Ty.fieldInfo_layout left, Option.bind_some,
    Option.bind_eq_some_iff, Option.map_eq_some_iff] at left right
  obtain ⟨_, _, _, selected, equal⟩ := left
  obtain ⟨_, _, _, otherSelected, otherEqual⟩ := right
  cases equal
  cases otherEqual
  exact Option.some.inj (selected.symm.trans otherSelected)

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

/-- Projecting an uncertain aggregate cannot manufacture definite availability. -/
theorem Initialization.select_maybe {program : Program} {parent : Ty}
    {path : List FieldKey} {selected : Initialization}
    (selection : Initialization.maybe.selectFields program parent path = some selected) : selected = .maybe := by
  induction path generalizing parent with
  | nil => exact (Option.some.inj selection).symm
  | cons key rest ih =>
    simp only [Initialization.selectFields, Option.bind_eq_some_iff] at selection
    obtain ⟨⟨index, child, types⟩, info, current, found, tail⟩ := selection
    have same : current = .maybe := (List.mem_replicate.mp (List.mem_of_getElem? found)).2
    subst current
    exact ih tail



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

/-- A disposable residual owner cannot contain a nondisposable selected child.
The proof follows the existing checked path and actual field-opening operation. -/
theorem PathType.disposable {program : Program} {home : Module} {parent child : Ty}
    {path : List FieldKey} (checked : PathType program home parent path child)
    {before : PartialValue} (permission : before.Disposable program parent) :
    ∃ selected, before.selectFields program parent path = some selected ∧
      selected.Disposable program child := by
  induction checked generalizing before with
  | here type => exact ⟨before, rfl, permission⟩
  | @step parent childType result key index rest projection path ih =>
    obtain ⟨beforeState, typed, disposition⟩ := permission
    obtain ⟨types, layout, fields, selected, opened, fieldsTyped⟩ := projection.open_partial typed
    obtain ⟨resident, state, found, stateFound, residentTyped⟩ := fieldsTyped.select selected
    have selectedPermission : resident.Disposable program childType := by
      refine Initialization.Disposable.realizes ?_ residentTyped
      cases disposition with
      | empty absent => exact .empty (absent.open_field stateFound)
      | permitted allowed => exact .permitted (projection.use_permission allowed)
      | tuple head tail =>
        simp only [Ty.fieldTypes, Option.some.injEq] at layout
        subst types
        exact (InitializationsDisposable.cons head tail).select selected stateFound
      | nominal declared restriction fieldPermissions =>
        simp only [Ty.fieldTypes, declared, Option.bind_some, Option.map_eq_some_iff] at layout
        obtain ⟨schema, chosen, rfl⟩ := layout
        exact (fieldPermissions none schema chosen).select selected stateFound
    obtain ⟨result, resultSelected, resultPermission⟩ := ih selectedPermission
    have info := projection.fieldInfo layout selected
    exact ⟨result, by simp [PartialValue.selectFields, info, opened, found, resultSelected], resultPermission⟩

/-- An observed descendant inherits disposal permission even when its ancestor
is only partially initialized and cannot itself be read. -/
theorem PartialValue.Disposable.selected_permission {program : Program} {home : Module}
    {parent child : Ty} {fields : List FieldKey} {before : PartialValue} {owner : Value}
    (permission : before.Disposable program parent)
    (path : PathType program home parent fields child)
    (read : ((before.selectFields program parent fields).bind PartialValue.read) = some owner) :
    UsePermitted program.data .discard child := by
  obtain ⟨selected, found, disposable⟩ := path.disposable permission
  rw [found] at read
  exact disposable.read_permission read

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

/-- Replacing the same path again removes the first update, including when
opening a whole resident exposed nested initialization fields. -/
theorem Initialization.write_overwrite {program : Program} {parent : Ty}
    {before middle after first second : Initialization} {path : List FieldKey}
    (written : before.writeFields program parent path first = some middle)
    (rewritten : middle.writeFields program parent path second = some after) :
    before.writeFields program parent path second = some after := by
  induction path generalizing parent before middle after with
  | nil => exact rewritten
  | cons key rest ih =>
    simp only [Initialization.writeFields, Option.bind_eq_some_iff, Option.map_eq_some_iff] at written
    obtain ⟨⟨index, child, types⟩, info, current, found, updated, tail, same⟩ := written
    subst middle
    have atIndex := List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1 (a := updated)
    simp only [Initialization.openFields] at atIndex
    simp only [Initialization.writeFields, info, Option.bind_some, Initialization.openFields, atIndex,
      Option.map_eq_some_iff] at rewritten
    obtain ⟨final, rewrittenTail, same⟩ := rewritten
    subst after
    simp [Initialization.writeFields, info, found, ih tail rewrittenTail]
    rfl

/-- The selected value transfers out; the shared field update exposes precisely
the remaining temporary aggregate whose residents will be discarded. -/
def Value.ProjectionCleanupSafe (program : Program) (home : Module) (aggregate : Value) (key : FieldKey) : Prop :=
  ∃ parent type index selected remainder,
    ValueHasType program aggregate parent ∧ ProjectionType program home parent key index type ∧
    aggregate.projectField program key = some (index, selected) ∧
    ValueHasType program selected type ∧
    (PartialValue.resident aggregate).writeFields program parent [key] .hole = some remainder ∧
    remainder.selectFields program parent [key] = some .hole ∧ remainder.Disposable program parent

theorem ProjectionType.cleanup_safe {program : Program} {home : Module} {parent type : Ty}
    {key : FieldKey} {index : Nat} {aggregate : Value} {residual : Initialization}
    (projection : ProjectionType program home parent key index type)
    (resident : ValueHasType program aggregate parent)
    (mask : Initialization.present.writeFields program parent [key] .absent = some residual)
    (discard : residual.Disposable program.data parent) :
    aggregate.ProjectionCleanupSafe program home key := by
  have path : PathType program home parent [key] type := .step projection (.here type)
  obtain ⟨remainder, state, writtenMask, written, remainderTyped, absent⟩ :=
    path.restore_partial resident.finite (.resident resident) (.hole type)
  cases Option.some.inj (writtenMask.symm.trans mask)
  obtain ⟨selected, found, selectedTyped, _⟩ := projection.access resident
  exact ⟨parent, type, index, selected, remainder, resident, projection, found, selectedTyped,
    written, absent, discard.realizes remainderTyped⟩


theorem ProjectionType.fieldInfo_exists {program : Program} {home : Module} {parent child : Ty}
    {key : FieldKey} {index : Nat} (projection : ProjectionType program home parent key index child) :
    ∃ types, parent.fieldInfo program key = some (index, child, types) := by
  cases projection with
  | @tuple first rest index child selected =>
    exact ⟨first :: rest, by simp [Ty.fieldInfo, Ty.fieldTypes, Ty.fieldIndex, selected]⟩
  | @nominal identity index declaration schema field key declared shape indexed selected visible =>
    exact ⟨schema.residents.map Field.type, by
      simp [Ty.fieldInfo, Ty.fieldTypes, Ty.fieldIndex, declared, DataDecl.constructor, shape,
        indexed, List.getElem?_map, selected]⟩

private theorem InitializationsApproximate.select {data : DataDeclarations}
    {types : List Ty} {before after : List Initialization}
    (joined : InitializationsApproximate data types before after)
    {index : Nat} {type : Ty} {state : Initialization}
    (selected : types[index]? = some type) (found : before[index]? = some state) :
    ∃ next, after[index]? = some next ∧ state.Approximates data type next := by
  induction types generalizing before after index with
  | nil => simp at selected
  | cons first rest ih =>
    cases joined with
    | cons head tail =>
      cases index with
      | zero => cases selected; cases found; exact ⟨_, rfl, head⟩
      | succ index => exact ih tail selected found

private theorem ProjectionType.approximate_field {program : Program} {home : Module}
    {parent child : Ty} {key : FieldKey} {index : Nat}
    (projection : ProjectionType program home parent key index child)
    {types : List Ty} (layout : parent.fieldTypes program = some types)
    (selected : types[index]? = some child)
    {before after state : Initialization} (joined : before.Approximates program.data parent after)
    (found : (before.openFields types.length)[index]? = some state) :
    ∃ next, (after.openFields types.length)[index]? = some next ∧
      state.Approximates program.data child next := by
  cases joined with
  | refl => exact ⟨state, found, .refl⟩
  | unknown disposable =>
    refine ⟨.maybe, ?_, .unknown (projection.use_permission disposable)⟩
    simp [Initialization.openFields, (List.getElem?_eq_some_iff.mp selected).1]
  | tuple children =>
    simp only [Ty.fieldTypes, Option.some.injEq] at layout
    subst types
    exact children.select selected found
  | nominal declared consumption children =>
    simp only [Ty.fieldTypes, declared, Option.bind_some, Option.map_eq_some_iff] at layout
    obtain ⟨schema, chosen, rfl⟩ := layout
    exact (children none schema chosen).select selected found

/-- Every descendant crosses a join under its own ownership permission. The
same actual resident realizes both masks; joining performs no storage mutation. -/
theorem PathType.approximate_initialization {program : Program} {home : Module}
    {parent child : Ty} {path : List FieldKey} (pathTyped : PathType program home parent path child)
    {value : PartialValue} {before after selectedState : Initialization}
    (typed : value.Typed program parent before)
    (joined : before.Approximates program.data parent after)
    (selected : before.selectFields program parent path = some selectedState) :
    ∃ next, after.selectFields program parent path = some next ∧
      selectedState.Approximates program.data child next := by
  induction pathTyped generalizing value before after with
  | here type => cases selected; exact ⟨after, rfl, joined⟩
  | step projection path ih =>
    obtain ⟨types, layout, fields, selectedType, opened, fieldsTyped⟩ := projection.open_partial typed
    obtain ⟨resident, state, found, stateFound, residentTyped⟩ := fieldsTyped.select selectedType
    have info := projection.fieldInfo layout selectedType
    simp only [Initialization.selectFields, info, Option.bind_some, stateFound] at selected
    obtain ⟨nextState, nextFound, fieldJoined⟩ := projection.approximate_field layout selectedType joined stateFound
    obtain ⟨next, nextSelected, nextJoined⟩ := ih residentTyped fieldJoined selected
    exact ⟨next, by simp [Initialization.selectFields, info, nextFound, nextSelected], nextJoined⟩

/-- Physical replacement frames every disjoint path, including failed reads and
partially consumed ancestors. No post-state typing premise is required. -/
theorem PathDisjoint.write_frame {program : Program} {home : Module} {parent : Ty}
    {writtenPath observedPath : List FieldKey}
    (apart : PathDisjoint program home parent writtenPath observedPath)
    {before after replacement : PartialValue}
    (written : before.writeFields program parent writtenPath replacement = some after) :
    after.selectFields program parent observedPath = before.selectFields program parent observedPath := by
  induction apart generalizing before after with
  | fork leftField rightField different =>
    obtain ⟨leftTypes, leftInfo⟩ := leftField.fieldInfo_exists
    obtain ⟨rightTypes, rightInfo⟩ := rightField.fieldInfo_exists
    rw [PartialValue.writeFields, leftInfo] at written
    simp only [Option.bind_some, Option.bind_eq_some_iff] at written
    obtain ⟨fields, opened, resident, found, updated, changed, closed⟩ := written
    have afterOpened := PartialValue.closeFields_open (program := program) closed
    simp [PartialValue.selectFields, rightInfo, afterOpened, opened, List.getElem?_set_ne different]
  | descend field apart ih =>
    obtain ⟨types, info⟩ := field.fieldInfo_exists
    rw [PartialValue.writeFields, info] at written
    simp only [Option.bind_some, Option.bind_eq_some_iff] at written
    obtain ⟨fields, opened, resident, found, updated, changed, closed⟩ := written
    have afterOpened := PartialValue.closeFields_open (program := program) closed
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simpa only [PartialValue.selectFields, info, Option.bind_some, afterOpened, opened, found,
      List.getElem?_set_self bound] using ih changed

/-- The same pre-state geometry frames the authoritative initialization mask. -/
theorem PathDisjoint.initialization_frame {program : Program} {home : Module} {parent : Ty}
    {writtenPath observedPath : List FieldKey}
    (apart : PathDisjoint program home parent writtenPath observedPath)
    {before after replacement : Initialization}
    (written : before.writeFields program parent writtenPath replacement = some after) :
    after.selectFields program parent observedPath = before.selectFields program parent observedPath := by
  induction apart generalizing before after with
  | fork leftField rightField different =>
    obtain ⟨leftTypes, leftInfo⟩ := leftField.fieldInfo_exists
    obtain ⟨rightTypes, rightInfo⟩ := rightField.fieldInfo_exists
    have layouts := Option.some.inj (Ty.fieldInfo_layout leftInfo |>.symm.trans (Ty.fieldInfo_layout rightInfo))
    subst rightTypes
    rw [Initialization.writeFields, leftInfo] at written
    simp only [Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at written
    obtain ⟨resident, found, updated, changed, same⟩ := written
    cases same
    simp [Initialization.selectFields, rightInfo, Initialization.openFields,
      List.getElem?_set_ne different]
  | descend field apart ih =>
    obtain ⟨types, info⟩ := field.fieldInfo_exists
    rw [Initialization.writeFields, info] at written
    simp only [Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at written
    obtain ⟨resident, found, updated, changed, same⟩ := written
    cases same
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [Initialization.openFields] at found bound
    simp only [Initialization.selectFields, info, Option.bind_some, Initialization.openFields]
    rw [List.getElem?_set_self bound, found]
    exact ih changed

/-- A selected static path admits replacement without a supplied future mask. -/
theorem Initialization.write_exists {program : Program} {parent : Ty}
    {before selected : Initialization} {path : List FieldKey}
    (selection : before.selectFields program parent path = some selected) (replacement : Initialization) :
    ∃ after, before.writeFields program parent path replacement = some after := by
  induction path generalizing before parent with
  | nil => exact ⟨replacement, rfl⟩
  | cons key rest ih =>
    simp only [Initialization.selectFields, Option.bind_eq_some_iff] at selection
    obtain ⟨⟨index, child, types⟩, info, current, found, tail⟩ := selection
    obtain ⟨updated, written⟩ := ih tail
    exact ⟨.fields ((before.openFields types.length).set index updated), by
      simp [Initialization.writeFields, info, found, written]⟩

/-- Resolved disjoint paths cannot designate the same syntactic path. -/
theorem PathDisjoint.ne {program : Program} {home : Module} {parent : Ty}
    {left right : List FieldKey} (apart : PathDisjoint program home parent left right) : left ≠ right := by
  induction apart with
  | fork leftField rightField different =>
    intro same
    have keys := (List.cons.inj same).1
    have leftIndex := leftField.fieldIndex
    have rightIndex := rightField.fieldIndex
    rw [keys] at leftIndex
    exact different (Option.some.inj (leftIndex.symm.trans rightIndex))
  | descend field apart ih =>
    intro same
    exact ih (List.cons.inj same).2

/-- Successful path replacement exposes exactly the inserted partial resident,
including a hole. This follows the actual update, without a typing premise. -/
theorem PartialValue.write_select {program : Program} {parent : Ty}
    {before after replacement : PartialValue} {path : List FieldKey}
    (written : before.writeFields program parent path replacement = some after) :
    after.selectFields program parent path = some replacement := by
  induction path generalizing parent before after with
  | nil => cases written; rfl
  | cons key rest ih =>
    simp only [PartialValue.writeFields, Option.bind_eq_some_iff] at written
    obtain ⟨⟨index, child, types⟩, info, fields, opened, current, found, updated, tail, closed⟩ := written
    have reopened := PartialValue.closeFields_open (program := program) closed
    have atIndex := List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1 (a := updated)
    simp only [PartialValue.selectFields, info, Option.bind_some, reopened, atIndex]
    exact ih tail

private theorem readPartialValues_none_of_member {values : List PartialValue} {value : PartialValue}
    (member : value ∈ values) (missing : value.read = none) : readPartialValues values = none := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    cases member with
    | head => simp [readPartialValues, missing]
    | tail _ member => simp [readPartialValues, ih member]

private theorem closeFields_read_none {parent : Ty} {fields : List PartialValue} {after : PartialValue}
    (closed : PartialValue.closeFields parent fields = some after)
    (missing : readPartialValues fields = none) : after.read = none := by
  cases parent <;> cases fields <;> simp [PartialValue.closeFields] at closed
  all_goals subst after
  case tuple.cons first rest head tail =>
    cases found : head.read with
    | none => simp [PartialValue.read, found]
    | some value =>
      have absent : readPartialValues tail = none := by simpa [readPartialValues, found] using missing
      simp [PartialValue.read, found, absent]
  all_goals simp [PartialValue.read, missing]

/-- Erasing any path prevents reconstruction of the whole owner. In particular,
consumption cannot turn an unavailable aggregate into a readable value. -/
theorem PartialValue.write_hole_unreadable {program : Program} {parent : Ty}
    {before after : PartialValue} {path : List FieldKey}
    (written : before.writeFields program parent path .hole = some after) : after.read = none := by
  induction path generalizing parent before after with
  | nil => cases written; simp [PartialValue.read]
  | cons key rest ih =>
    simp only [PartialValue.writeFields, Option.bind_eq_some_iff] at written
    obtain ⟨⟨index, child, types⟩, info, fields, opened, current, found, updated, tail, closed⟩ := written
    apply closeFields_read_none closed
    apply readPartialValues_none_of_member
      (List.mem_of_getElem? (List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1))
    exact ih tail

private theorem hole_open_fields {program : Program} {parent : Ty} {fields : List PartialValue}
    (opened : PartialValue.hole.openFields program parent = some fields) :
    ∃ count, fields = List.replicate count PartialValue.hole := by
  cases parent <;> simp only [PartialValue.openFields] at opened
  all_goals try contradiction
  case tuple first rest => cases opened; exact ⟨_, rfl⟩
  case nominal identity =>
    obtain ⟨declaration, _, rest⟩ := Option.bind_eq_some_iff.mp opened
    obtain ⟨schema, _, same⟩ := Option.map_eq_some_iff.mp rest
    cases same
    exact ⟨_, rfl⟩

private theorem hole_select_read_none (program : Program) (parent : Ty) (path : List FieldKey) :
    ((PartialValue.hole.selectFields program parent path).bind PartialValue.read) = none := by
  induction path generalizing parent with
  | nil => simp [PartialValue.selectFields, PartialValue.read]
  | cons key rest ih =>
    cases info : parent.fieldInfo program key with
    | none => simp [PartialValue.selectFields, info]
    | some data =>
      obtain ⟨index, child, types⟩ := data
      cases opened : PartialValue.hole.openFields program parent with
      | none => simp [PartialValue.selectFields, info, opened]
      | some fields =>
        obtain ⟨count, rfl⟩ := hole_open_fields opened
        cases found : (List.replicate count PartialValue.hole)[index]? with
        | none => simp [PartialValue.selectFields, info, opened, found]
        | some value =>
          have same := (List.mem_replicate.mp (List.mem_of_getElem? found)).2
          subst value
          simpa [PartialValue.selectFields, info, opened, found] using ih child

/-- An erasure cannot introduce or change any readable descendant. Observed
and erased paths may overlap; no separation or future-readiness is assumed. -/
theorem PartialValue.write_hole_read_before {program : Program} {parent : Ty}
    {before after : PartialValue} {writtenPath observedPath : List FieldKey} {value : Value}
    (written : before.writeFields program parent writtenPath .hole = some after)
    (read : (after.selectFields program parent observedPath).bind PartialValue.read = some value) :
    (before.selectFields program parent observedPath).bind PartialValue.read = some value := by
  induction writtenPath generalizing parent before after observedPath with
  | nil =>
    cases written
    rw [hole_select_read_none] at read
    contradiction
  | cons key rest ih =>
    cases observedPath with
    | nil =>
      simp only [PartialValue.selectFields, Option.bind_some] at read
      rw [PartialValue.write_hole_unreadable written] at read
      contradiction
    | cons observed tail =>
      simp only [PartialValue.writeFields, Option.bind_eq_some_iff] at written
      obtain ⟨⟨index, child, types⟩, info, fields, opened, current, found, updated, changed, closed⟩ := written
      have reopened := PartialValue.closeFields_open (program := program) closed
      cases observedInfo : parent.fieldInfo program observed with
      | none => simp [PartialValue.selectFields, observedInfo] at read
      | some data =>
        obtain ⟨other, observedType, observedTypes⟩ := data
        simp only [PartialValue.selectFields, observedInfo, Option.bind_some, reopened,
          opened] at read ⊢
        by_cases same : other = index
        · subst other
          have childSame := Ty.fieldInfo_child_unique observedInfo info
          subst observedType
          have atIndex := List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1 (a := updated)
          simp only [atIndex, Option.bind_some] at read
          simp only [found, Option.bind_some]
          exact ih changed read
        · simpa only [List.getElem?_set_ne (Ne.symm same)] using read

private theorem empty_open_fields {program : Program} {parent : Ty} {before : PartialValue}
    {fields : List PartialValue} (empty : before.Empty)
    (opened : before.openFields program parent = some fields) :
    ∀ value ∈ fields, value.Empty := by
  cases before with
  | hole =>
    obtain ⟨count, rfl⟩ := hole_open_fields opened
    intro value member
    have same := (List.mem_replicate.mp member).2
    subst value
    trivial
  | resident value => simp [PartialValue.Empty] at empty
  | tuple head tail =>
    cases parent <;> simp_all [PartialValue.openFields, PartialValue.Empty]
    subst fields
    simpa only [List.mem_cons, forall_eq_or_imp] using empty
  | nominal identity tag values =>
    cases parent <;> cases tag <;> simp_all [PartialValue.openFields, PartialValue.Empty]

private theorem empty_close_fields {parent : Ty} {fields : List PartialValue} {after : PartialValue}
    (closed : PartialValue.closeFields parent fields = some after) (nonempty : fields ≠ [])
    (empty : ∀ value ∈ fields, value.Empty) : after.Empty := by
  cases parent <;> cases fields <;> simp_all [PartialValue.closeFields]
  all_goals subst after; simp_all [PartialValue.Empty]

/-- Erasure preserves actual structural absence, not merely failure to read a
whole aggregate. This also protects zero-field nominal ownership distinctions. -/
theorem PartialValue.Empty.write_hole {program : Program} {parent : Ty}
    {before after : PartialValue} {path : List FieldKey} (empty : before.Empty)
    (written : before.writeFields program parent path .hole = some after) : after.Empty := by
  induction path generalizing parent before after with
  | nil => cases written; simp [PartialValue.Empty]
  | cons key rest ih =>
    simp only [PartialValue.writeFields, Option.bind_eq_some_iff] at written
    obtain ⟨⟨index, child, types⟩, info, fields, opened, current, found, updated, changed, closed⟩ := written
    have allEmpty := empty_open_fields empty opened
    have updatedEmpty := ih (allEmpty current (List.mem_of_getElem? found)) changed
    apply empty_close_fields closed
    · have bound := (List.getElem?_eq_some_iff.mp found).1
      intro absent
      have length := congrArg List.length absent
      simp only [List.length_set, List.length_nil] at length
      omega
    · intro value member
      rcases List.mem_or_eq_of_mem_set member with original | same
      · exact allEmpty value original
      · subst value; exact updatedEmpty

theorem PartialValue.Empty.selected {program : Program} {parent : Ty}
    {before selected : PartialValue} {path : List FieldKey} (empty : before.Empty)
    (found : before.selectFields program parent path = some selected) : selected.Empty := by
  induction path generalizing parent before with
  | nil => cases found; exact empty
  | cons key rest ih =>
    simp only [PartialValue.selectFields, Option.bind_eq_some_iff] at found
    obtain ⟨⟨index, child, types⟩, info, fields, opened, current, atIndex, selected⟩ := found
    exact ih (empty_open_fields empty opened current (List.mem_of_getElem? atIndex)) selected

/-- Consumption cannot recreate ownership in an empty descendant, even when
an ancestor or overlapping path is erased. This is stronger than read failure. -/
theorem PartialValue.Empty.write_hole_selected {program : Program} {parent : Ty}
    {before after : PartialValue} {writtenPath observedPath : List FieldKey}
    (empty : ∀ original, before.selectFields program parent observedPath = some original → original.Empty)
    (written : before.writeFields program parent writtenPath .hole = some after) :
    ∀ selected, after.selectFields program parent observedPath = some selected → selected.Empty := by
  induction writtenPath generalizing parent before after observedPath with
  | nil =>
    cases written
    intro selected later
    exact PartialValue.Empty.selected (by simp [PartialValue.Empty]) later
  | cons key rest ih =>
    cases observedPath with
    | nil =>
      intro selected later
      cases later
      exact (empty before rfl).write_hole written
    | cons observed tail =>
      intro selected later
      simp only [PartialValue.writeFields, Option.bind_eq_some_iff] at written
      obtain ⟨⟨index, child, types⟩, info, fields, opened, current, found, updated, changed, closed⟩ := written
      have reopened := PartialValue.closeFields_open (program := program) closed
      cases observedInfo : parent.fieldInfo program observed with
      | none => simp [PartialValue.selectFields, observedInfo] at later
      | some data =>
        obtain ⟨other, observedType, observedTypes⟩ := data
        simp only [PartialValue.selectFields, observedInfo, Option.bind_some, opened] at empty
        simp only [PartialValue.selectFields, observedInfo, Option.bind_some, reopened] at later
        by_cases same : other = index
        · subst other
          have childSame := Ty.fieldInfo_child_unique observedInfo info
          subst observedType
          have atIndex := List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1 (a := updated)
          simp only [found, Option.bind_some] at empty
          simp only [atIndex, Option.bind_some] at later
          exact ih empty changed selected later
        · rw [List.getElem?_set_ne (Ne.symm same)] at later
          exact empty selected later

theorem Initialization.Empty.write_absent {program : Program} {parent : Ty}
    {before after : Initialization} {path : List FieldKey} (empty : before.Empty)
    (written : before.writeFields program parent path .absent = some after) : after.Empty := by
  induction path generalizing parent before after with
  | nil => cases written; simp [Initialization.Empty]
  | cons key rest ih =>
    simp only [Initialization.writeFields, Option.bind_eq_some_iff, Option.map_eq_some_iff] at written
    obtain ⟨⟨index, child, types⟩, info, current, found, updated, changed, rfl⟩ := written
    have updatedEmpty := ih (empty.open_field found) changed
    simp only [Initialization.Empty]
    refine ⟨?_, ?_⟩
    · intro equal
      have bound := (List.getElem?_eq_some_iff.mp found).1
      have length := congrArg List.length equal
      simp only [List.length_set, List.length_nil] at length
      dsimp only at length bound
      omega
    · intro value member
      rcases List.mem_or_eq_of_mem_set member with original | same
      · obtain ⟨position, selected⟩ := List.mem_iff_getElem?.mp original
        exact empty.open_field selected
      · subst value; exact updatedEmpty

private theorem InitializationsDisposable.replace {data : DataDeclarations}
    {types : List Ty} {states : List Initialization} (permission : InitializationsDisposable data types states)
    {index : Nat} {type : Ty} {replacement : Initialization}
    (selected : types[index]? = some type) (allowed : replacement.Disposable data type) :
    InitializationsDisposable data types (states.set index replacement) := by
  induction types generalizing states index with
  | nil => simp at selected
  | cons first rest ih =>
    cases permission with
    | cons head tail =>
      cases index with
      | zero => cases selected; exact .cons allowed tail
      | succ index => exact .cons head (ih tail selected)

private theorem InitializationsDisposable.tuple_permission {data : DataDeclarations}
    {first : Ty} {rest : List Ty} {states : List Initialization}
    (permission : InitializationsDisposable data (first :: rest) states) :
    (Initialization.fields states).Disposable data (.tuple first rest) := by
  cases permission with
  | cons head tail => exact .tuple head tail

/-- Consuming any field preserves an existing residual disposal permission. The
same mask update drives both source checking and actual storage realization. -/
theorem Initialization.Disposable.write_absent {program : Program} {parent : Ty}
    {before after : Initialization} {path : List FieldKey}
    (permission : before.Disposable program.data parent)
    (written : before.writeFields program parent path .absent = some after) :
    after.Disposable program.data parent := by
  induction path generalizing parent before after with
  | nil => cases written; exact .empty (by simp [Initialization.Empty])
  | cons key rest ih =>
    cases permission with
    | empty absent => exact .empty (absent.write_absent written)
    | permitted allowed => exact .permitted allowed
    | tuple head tail =>
      simp only [Initialization.writeFields, Option.bind_eq_some_iff, Option.map_eq_some_iff] at written
      obtain ⟨⟨index, child, types⟩, info, current, found, updated, changed, rfl⟩ := written
      have layout := Ty.fieldInfo_layout info
      simp only [Ty.fieldTypes, Option.some.injEq] at layout
      subst types
      have selected : _ := info
      simp only [Ty.fieldInfo, Ty.fieldTypes, Option.bind_some,
        Option.bind_eq_some_iff, Option.map_eq_some_iff] at selected
      obtain ⟨_, indexed, _, selected, equal⟩ := selected
      cases equal
      have all := InitializationsDisposable.cons head tail
      have replaced := all.replace selected (ih (all.select selected found) changed)
      exact replaced.tuple_permission
    | @nominal identity declaration states declared restriction fields =>
      simp only [Initialization.writeFields, Option.bind_eq_some_iff, Option.map_eq_some_iff] at written
      obtain ⟨⟨index, child, types⟩, info, current, found, updated, changed, rfl⟩ := written
      have layout := Ty.fieldInfo_layout info
      simp only [Ty.fieldTypes, declared, Option.bind_some, Option.map_eq_some_iff] at layout
      obtain ⟨schema, chosen, rfl⟩ := layout
      have selected : _ := info
      simp only [Ty.fieldInfo, Ty.fieldTypes, declared, Option.bind_some, chosen,
        Option.map_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at selected
      obtain ⟨_, indexed, _, selected, equal⟩ := selected
      cases equal
      have all := fields none schema chosen
      have replaced := all.replace selected (ih (all.select selected found) changed)
      refine .nominal declared restriction ?_
      intro tag candidate constructor
      cases shape : declaration.shape with
      | «structure» residents =>
        simp only [DataDecl.constructor, shape, Option.some.injEq] at chosen
        subst schema
        cases tag <;> simp_all [DataDecl.constructor, Initialization.openFields]
      | enumeration variants nonexhaustive => simp [DataDecl.constructor, shape] at chosen

/-- The actual erasure preserves residual disposal permission. Static and
runtime updates are the paired products of the existing checked path producer. -/
theorem PartialValue.Disposable.write_hole {program : Program} {parent child : Ty}
    {before after : PartialValue} {home : Module} {path : List FieldKey}
    (permission : before.Disposable program parent)
    (finite : FiniteLayout program.target program.data parent)
    (checked : PathType program home parent path child)
    (written : before.writeFields program parent path .hole = some after) :
    after.Disposable program parent := by
  obtain ⟨state, typed, disposition⟩ := permission
  obtain ⟨actual, next, stateWritten, actualWritten, actualTyped, _⟩ :=
    checked.restore_partial finite typed (.hole child)
  cases Option.some.inj (actualWritten.symm.trans written)
  exact ⟨next, actualTyped, disposition.write_absent stateWritten⟩

end Grounded
