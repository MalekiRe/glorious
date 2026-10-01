import Grounded.Values

/-! Shared field and path authority, independent of lexical environments. -/
namespace Grounded

/-- One checked field projection, shared by rvalue projection and rooted places. -/
inductive ProjectionType (program : Program) (home : Module) : Ty → FieldKey → Nat → Ty → Prop where
  | tuple {first : Ty} {rest : List Ty} {index : Nat} {type : Ty}
      (selected : (first :: rest)[index]? = some type) :
      ProjectionType program home (.tuple first rest) (.positional index) index type
  | nominal {identity index : Nat} {declaration : DataDecl} {schema : Fields} {field : Field} {key : FieldKey}
      (declared : program.data identity = some declaration)
      (structureOnly : declaration.shape = .structure schema)
      (indexed : schema.index key = some index) (selected : schema.residents[index]? = some field)
      (visible : field.visibility.Allows declaration.home home) :
      ProjectionType program home (.nominal identity) key index field.type

inductive PathType (program : Program) (home : Module) : Ty → List FieldKey → Ty → Prop where
  | here (type : Ty) : PathType program home type [] type
  | step {parent child result : Ty} {key : FieldKey} {index : Nat} {rest : List FieldKey}
      (field : ProjectionType program home parent key index child)
      (tail : PathType program home child rest result) :
      PathType program home parent (key :: rest) result

/-- Resolve one tuple/struct field; enum payloads are not unchecked places. -/
def Value.projectField (program : Program) (value : Value) (key : FieldKey) : Option (Nat × Value) :=
  match value, key with
  | .tuple head tail, .positional index => ((head :: tail)[index]?).map (index, ·)
  | .nominal identity none fields, key => do
      let declaration ← program.data identity
      let schema ← declaration.constructor none
      let index ← schema.index key
      let resident ← fields[index]?
      pure (index, resident)
  | _, _ => none

/-- Replace precisely one existing resident, retaining the constructor and siblings. -/
def Value.replaceField (value : Value) (index : Nat) (replacement : Value) : Option Value :=
  match value, index with
  | .tuple _ tail, 0 => some (.tuple replacement tail)
  | .tuple head tail, index + 1 => (tail[index]?).map (fun _ => .tuple head (tail.set index replacement))
  | .nominal identity tag fields, index =>
      (fields[index]?).map (fun _ => .nominal identity tag (fields.set index replacement))
  | _, _ => none

def readFields (program : Program) (value : Value) : List FieldKey → Option Value
  | [] => some value
  | key :: rest => do
      let (_, child) ← value.projectField program key
      readFields program child rest

def writeFields (program : Program) (value : Value) (fields : List FieldKey)
    (replacement : Value) : Option Value :=
  match fields with
  | [] => some replacement
  | key :: rest => do
      let (index, child) ← value.projectField program key
      let updated ← writeFields program child rest replacement
      value.replaceField index updated

variable {program : Program} {home : Module}

theorem ValuesHaveTypes.set {values : List Value} {types : List Ty}
    (typed : ValuesHaveTypes program values types) {index : Nat} {type : Ty} {value : Value}
    (selected : types[index]? = some type) (resident : ValueHasType program value type) :
    ValuesHaveTypes program (values.set index value) types := by
  induction types generalizing values index with
  | nil => simp at selected
  | cons first rest ih =>
    cases typed with
    | cons firstTyped restTyped =>
      cases index with
      | zero => cases selected; exact .cons resident restTyped
      | succ index => exact .cons firstTyped (ih restTyped selected)

/-- Every sibling is preserved by an actual successful one-field replacement. -/
theorem Value.replaceField_siblings {before after replacement : Value} {index other : Nat}
    (written : before.replaceField index replacement = some after) (different : index ≠ other) :
    after.children[other]? = before.children[other]? := by
  cases before with
  | unit => simp [Value.replaceField] at written
  | integer type number => simp [Value.replaceField] at written
  | character number => simp [Value.replaceField] at written
  | array values => simp [Value.replaceField] at written
  | tuple head tail =>
    cases index with
    | zero =>
      cases written
      cases other with
      | zero => exact False.elim (different rfl)
      | succ other => rfl
    | succ index =>
      cases selected : tail[index]? with
      | none => simp [Value.replaceField, selected] at written
      | some old =>
        simp [Value.replaceField, selected] at written
        subst after
        cases other with
        | zero => rfl
        | succ other =>
          have distinct : index ≠ other := fun same => different (congrArg Nat.succ same)
          simp [Value.children, distinct]
  | nominal identity tag fields =>
    cases selected : fields[index]? with
    | none => simp [Value.replaceField, selected] at written
    | some old =>
      simp [Value.replaceField, selected] at written
      subst after
      simp [Value.children, different]

/-- Static field authority and current value typing construct selection, typed
replacement and exact readback. Runtime success is not a checking premise. -/
theorem ProjectionType.access {parent type : Ty} {key : FieldKey} {index : Nat} {value : Value}
    (projection : ProjectionType program home parent key index type)
    (typed : ValueHasType program value parent) :
    ∃ child, value.projectField program key = some (index, child) ∧ ValueHasType program child type ∧
      ∀ replacement, ValueHasType program replacement type →
        ∃ after, value.replaceField index replacement = some after ∧ ValueHasType program after parent ∧
          after.projectField program key = some (index, replacement) := by
  cases projection with
  | tuple selected =>
    cases typed with
    | tuple first rest =>
      cases index with
      | zero =>
        cases selected
        refine ⟨_, rfl, first, ?_⟩
        intro replacement resident
        exact ⟨_, rfl, .tuple resident rest, rfl⟩
      | succ index =>
        obtain ⟨child, found, childTyped⟩ := rest.select index _ selected
        obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
        refine ⟨child, by simp [Value.projectField, found], childTyped, ?_⟩
        intro replacement resident
        refine ⟨_, by simp [Value.replaceField, found], .tuple first (rest.set selected resident), ?_⟩
        simp [Value.projectField, List.getElem?_set_self bound]
  | @nominal identity index declaration schema field key declared structureOnly indexed selected visible =>
    cases typed with
    | @nominal _ tag otherDeclaration otherSchema values otherDeclared chosen finite residents =>
      have sameDeclaration := Option.some.inj (otherDeclared.symm.trans declared)
      subst otherDeclaration
      cases tag with
      | some tag => simp [DataDecl.constructor, structureOnly] at chosen
      | none =>
        have sameSchema : otherSchema = schema := by
          simpa [DataDecl.constructor, structureOnly] using chosen.symm
        subst otherSchema
        have fieldType : (schema.residents.map Field.type)[index]? = some field.type := by
          simp [List.getElem?_map, selected]
        obtain ⟨child, found, childTyped⟩ := residents.select index _ fieldType
        obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
        refine ⟨child, by simp [Value.projectField, declared, DataDecl.constructor, structureOnly, indexed, found], childTyped, ?_⟩
        intro replacement resident
        refine ⟨_, by simp [Value.replaceField, found], .nominal declared chosen finite (residents.set fieldType resident), ?_⟩
        simp [Value.projectField, declared, DataDecl.constructor, structureOnly, indexed, List.getElem?_set_self bound]

theorem PathType.read {parent type : Ty} {fields : List FieldKey} {value : Value}
    (path : PathType program home parent fields type) (typed : ValueHasType program value parent) :
    ∃ result, readFields program value fields = some result ∧ ValueHasType program result type := by
  induction path generalizing value with
  | here type => exact ⟨value, rfl, typed⟩
  | step field tail ih =>
    obtain ⟨child, selected, childTyped, _⟩ := field.access typed
    obtain ⟨result, read, resultTyped⟩ := ih childTyped
    exact ⟨result, by simp [readFields, selected, read], resultTyped⟩

theorem PathType.write {parent type : Ty} {fields : List FieldKey} {value replacement : Value}
    (path : PathType program home parent fields type) (typed : ValueHasType program value parent)
    (resident : ValueHasType program replacement type) :
    ∃ after, writeFields program value fields replacement = some after ∧ ValueHasType program after parent ∧
      readFields program after fields = some replacement := by
  induction path generalizing value with
  | here type => exact ⟨replacement, rfl, resident, rfl⟩
  | step field tail ih =>
    obtain ⟨child, selected, childTyped, replace⟩ := field.access typed
    obtain ⟨updated, written, updatedTyped, readBack⟩ := ih childTyped resident
    obtain ⟨after, replaced, afterTyped, selectedAfter⟩ := replace updated updatedTyped
    exact ⟨after, by simp [writeFields, selected, written, replaced], afterTyped,
      by simp [readFields, selectedAfter, readBack]⟩

/-- A nested write preserves every sibling of its selected first field.
The same law applies recursively at each prefix of the written path. -/
theorem writeFields_siblings {program : Program} {before after replacement child : Value}
    {key : FieldKey} {rest : List FieldKey} {index other : Nat}
    (selected : before.projectField program key = some (index, child))
    (written : writeFields program before (key :: rest) replacement = some after)
    (different : index ≠ other) : after.children[other]? = before.children[other]? := by
  simp only [writeFields, selected] at written
  cases childWrite : writeFields program child rest replacement with
  | none => simp [childWrite] at written
  | some updated =>
    simp [childWrite] at written
    exact Value.replaceField_siblings written different

end Grounded
