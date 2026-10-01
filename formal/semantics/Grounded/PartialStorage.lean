import Grounded.RuntimeHeap
import Grounded.Values

/-! Resident availability is distinct from the lifetime of its storage cell.
A hole contains no old value. Partial aggregates retain only their actual
remaining residents and constructor identity. -/
namespace Grounded

inductive Initialization where
  | absent
  | present
  | fields (states : List Initialization)

mutual
inductive Initialization.Ready : Initialization → Prop where
  | present : Initialization.Ready .present
  | fields {states : List Initialization} (residents : InitializationsReady states) :
      Initialization.Ready (.fields states)
inductive InitializationsReady : List Initialization → Prop where
  | nil : InitializationsReady []
  | cons {head : Initialization} {tail : List Initialization}
      (first : Initialization.Ready head) (rest : InitializationsReady tail) :
      InitializationsReady (head :: tail)
end

inductive PartialValue where
  | hole
  | resident (value : Value)
  | tuple (head : PartialValue) (tail : List PartialValue)
  | nominal (identity : Nat) (tag : Option Nat) (fields : List PartialValue)

mutual
def PartialValue.read : PartialValue → Option Value
  | .hole => none
  | .resident value => some value
  | .tuple head tail => head.read.bind (fun first =>
      readPartialValues tail |>.map (fun rest => .tuple first rest))
  | .nominal identity tag fields => (readPartialValues fields).map (.nominal identity tag)
termination_by value => sizeOf value

def readPartialValues : List PartialValue → Option (List Value)
  | [] => some []
  | head :: tail => head.read.bind (fun first => (readPartialValues tail).map (first :: ·))
termination_by values => sizeOf values
end

mutual
inductive PartialValue.Typed (program : Program) : PartialValue → Ty → Initialization → Prop where
  | hole (type : Ty) : PartialValue.Typed program .hole type .absent
  | resident {value : Value} {type : Ty} (typed : ValueHasType program value type) :
      PartialValue.Typed program (.resident value) type .present
  | tuple {head : PartialValue} {tail : List PartialValue} {first : Ty} {rest : List Ty}
      {headState : Initialization} {tailStates : List Initialization}
      (headTyped : PartialValue.Typed program head first headState)
      (tailTyped : PartialValuesTyped program tail rest tailStates) :
      PartialValue.Typed program (.tuple head tail) (.tuple first rest) (.fields (headState :: tailStates))
  | nominal {identity : Nat} {tag : Option Nat} {declaration : DataDecl} {schema : Fields}
      {fields : List PartialValue} {states : List Initialization}
      (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (residents : PartialValuesTyped program fields (schema.residents.map Field.type) states) :
      PartialValue.Typed program (.nominal identity tag fields) (.nominal identity) (.fields states)
inductive PartialValuesTyped (program : Program) : List PartialValue → List Ty → List Initialization → Prop where
  | nil : PartialValuesTyped program [] [] []
  | cons {head : PartialValue} {tail : List PartialValue} {first : Ty} {rest : List Ty}
      {headState : Initialization} {tailStates : List Initialization}
      (headTyped : PartialValue.Typed program head first headState)
      (tailTyped : PartialValuesTyped program tail rest tailStates) :
      PartialValuesTyped program (head :: tail) (first :: rest) (headState :: tailStates)
end

/-- Checking availability constructs the actual read; successful reads are not
part of the availability premise. -/
theorem PartialValue.Typed.read {program : Program} {valueState : PartialValue} {type : Ty}
    {state : Initialization} (typed : valueState.Typed program type state)
    (ready : state.Ready) :
    ∃ value, valueState.read = some value ∧ ValueHasType program value type := by
  induction typed using PartialValue.Typed.rec
    (motive_2 := fun partials types states _ => InitializationsReady states →
      ∃ values, readPartialValues partials = some values ∧ ValuesHaveTypes program values types) with
  | hole => cases ready
  | resident resident => exact ⟨_, by simp [PartialValue.read], resident⟩
  | tuple head tail headIH tailIH =>
    cases ready with
    | fields residents =>
      cases residents with
      | cons first rest =>
        obtain ⟨value, readHead, valueTyped⟩ := headIH first
        obtain ⟨values, readTail, valuesTyped⟩ := tailIH rest
        exact ⟨_, by simp [PartialValue.read, readHead, readTail], .tuple valueTyped valuesTyped⟩
  | nominal declared chosen finite residents ih =>
    cases ready with
    | fields ready =>
      obtain ⟨values, read, typed⟩ := ih ready
      exact ⟨_, by simp [PartialValue.read, read], .nominal declared chosen finite typed⟩
  | nil => exact ⟨[], by simp [readPartialValues], .nil⟩
  | cons head tail headIH tailIH =>
    rename_i ready
    cases ready with
    | cons first rest =>
      obtain ⟨value, readHead, valueTyped⟩ := headIH first
      obtain ⟨values, readTail, valuesTyped⟩ := tailIH rest
      exact ⟨_, by simp [readPartialValues, readHead, readTail], .cons valueTyped valuesTyped⟩

/-- No initialization claim can be manufactured from an empty resident. -/
theorem PartialValue.Typed.hole_unready {program : Program} {type : Ty} {state : Initialization}
    (typed : PartialValue.Typed program .hole type state) : ¬state.Ready := by
  cases typed
  intro ready
  cases ready

/-- No active resident remains, including nested aggregate shells. -/
def Initialization.Empty : Initialization → Prop
  | .absent => True
  | .present => False
  | .fields states => ∀ state ∈ states, state.Empty

def PartialValue.Empty : PartialValue → Prop
  | .hole => True
  | .resident _ => False
  | .tuple head tail => head.Empty ∧ ∀ value ∈ tail, value.Empty
  | .nominal _ _ fields => ∀ value ∈ fields, value.Empty

/-- The shared initialization mask certifies actual absence, not just a readable
value's absence. No resident can hide inside an empty partial aggregate. -/
theorem PartialValue.Typed.empty {program : Program} {value : PartialValue} {type : Ty}
    {state : Initialization} (typed : value.Typed program type state) (empty : state.Empty) : value.Empty := by
  induction typed using PartialValue.Typed.rec
    (motive_2 := fun values _ states _ =>
      (∀ state ∈ states, state.Empty) → ∀ value ∈ values, value.Empty)
  all_goals simp_all [Initialization.Empty, PartialValue.Empty]
  case cons =>
    rename_i value headEmpty tailEmpty states member
    rcases member with rfl | member
    · exact headEmpty
    · exact tailEmpty value member

mutual
/-- Residual disposition uses initialization masks, not the original whole-owner
class. Nominal restrictions still constrain every nonempty residual shell. -/
inductive Initialization.Disposable (data : DataDeclarations) : Ty → Initialization → Prop where
  | empty {type state} (absent : state.Empty) : Initialization.Disposable data type state
  | permitted {type state} (permission : UsePermitted data .discard type) : Initialization.Disposable data type state
  | tuple {first rest head tail}
      (headPermission : Initialization.Disposable data first head)
      (tailPermission : InitializationsDisposable data rest tail) :
      Initialization.Disposable data (.tuple first rest) (.fields (head :: tail))
  | nominal {identity declaration states}
      (declared : data identity = some declaration)
      (restriction : UsePermission.discard.Allows declaration.restriction)
      (fields : ∀ tag schema, declaration.constructor tag = some schema →
        InitializationsDisposable data (schema.residents.map Field.type) states) :
      Initialization.Disposable data (.nominal identity) (.fields states)
inductive InitializationsDisposable (data : DataDeclarations) : List Ty → List Initialization → Prop where
  | nil : InitializationsDisposable data [] []
  | cons {type types state states} (head : Initialization.Disposable data type state)
      (tail : InitializationsDisposable data types states) :
      InitializationsDisposable data (type :: types) (state :: states)
end

/-- Runtime interpretation of residual permission. The witnesses concern the
actual retained residents, never a reconstructed source flow or future state. -/
inductive PartialValue.Disposable (program : Program) : PartialValue → Prop where
  | empty {value} (absent : value.Empty) : Disposable program value
  | permitted {value type state} (typed : PartialValue.Typed program value type state)
      (permission : UsePermitted program.data .discard type) : Disposable program value
  | tuple {head tail} (first : Disposable program head)
      (rest : ∀ value ∈ tail, Disposable program value) : Disposable program (.tuple head tail)
  | nominal {identity tag declaration schema fields}
      (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some schema)
      (restriction : UsePermission.discard.Allows declaration.restriction)
      (residents : ∀ value ∈ fields, Disposable program value) :
      Disposable program (.nominal identity tag fields)

theorem Initialization.Disposable.realizes {program : Program} {type : Ty} {state : Initialization}
    (permission : state.Disposable program.data type) {value : PartialValue}
    (typed : value.Typed program type state) : value.Disposable program := by
  induction permission using Initialization.Disposable.rec
    (motive_2 := fun types states _ => ∀ values, PartialValuesTyped program values types states →
      ∀ value ∈ values, value.Disposable program) generalizing value with
  | empty absent => exact .empty (typed.empty absent)
  | permitted permission => exact .permitted typed permission
  | tuple head tail headIH tailIH =>
    cases typed with
    | tuple first rest => exact .tuple (headIH first) (tailIH _ rest)
  | nominal declared restriction fields ih =>
    cases typed with
    | nominal found chosen finite residents =>
      cases Option.some.inj (declared.symm.trans found)
      exact .nominal found chosen restriction (ih _ _ chosen _ residents)
  | nil => rename_i values typed value member; cases typed; cases member
  | cons head tail headIH tailIH =>
    rename_i values typed value member
    cases typed with
    | cons first rest =>
      cases member with
      | head => exact headIH first
      | tail _ member => exact tailIH _ rest value member

/-- A still-whole resident receives exactly its ordinary MayDiscard permission. -/
theorem Initialization.Disposable.present_iff {data : DataDeclarations} {type : Ty} :
    Initialization.present.Disposable data type ↔ UsePermitted data .discard type := by
  constructor
  · intro permission
    cases permission with
    | empty absent => simp [Initialization.Empty] at absent
    | permitted permission => exact permission
  · exact .permitted

/-- Explicit exact restrictions cannot be bypassed by partially consuming fields. -/
theorem Initialization.Disposable.exact_nominal_empty {data : DataDeclarations} {identity : Nat}
    {declaration : DataDecl} {state : Initialization}
    (declared : data identity = some declaration) (restricted : declaration.restriction = some .exact)
    (permission : state.Disposable data (.nominal identity)) : state.Empty := by
  cases permission with
  | empty absent => exact absent
  | permitted permission =>
    cases permission with
    | nominal found restriction fields =>
      cases Option.some.inj (found.symm.trans declared)
      simp [UsePermission.Allows, restricted] at restriction
  | nominal found restriction fields =>
    cases Option.some.inj (found.symm.trans declared)
    simp [UsePermission.Allows, restricted] at restriction

/-- The same exclusion holds for the actual retained nominal shell. -/
theorem PartialValue.Disposable.exact_nominal_empty {program : Program} {identity : Nat}
    {declaration : DataDecl} {tag : Option Nat} {fields : List PartialValue}
    (declared : program.data identity = some declaration) (restricted : declaration.restriction = some .exact)
    (permission : (PartialValue.nominal identity tag fields).Disposable program) :
    ∀ value ∈ fields, value.Empty := by
  cases permission with
  | empty absent => simpa [PartialValue.Empty] using absent
  | permitted typed allowed =>
    cases typed with
    | nominal found chosen finite residents =>
      cases allowed with
      | nominal other restriction fields =>
        cases Option.some.inj (other.symm.trans declared)
        simp [UsePermission.Allows, restricted] at restriction
  | nominal found chosen restriction residents =>
    cases Option.some.inj (found.symm.trans declared)
    simp [UsePermission.Allows, restricted] at restriction

/-- A live exact nominal value is never an empty shell, even with zero fields. -/
theorem PartialValue.Disposable.not_exact_resident {program : Program} {identity : Nat}
    {declaration : DataDecl} {tag : Option Nat} {fields : List Value}
    (declared : program.data identity = some declaration)
    (restricted : declaration.restriction = some .exact) :
    ¬ (PartialValue.resident (.nominal identity tag fields)).Disposable program := by
  intro permission
  cases permission with
  | empty absent => simp [PartialValue.Empty] at absent
  | permitted typed allowed =>
    cases typed with
    | resident typed =>
      cases typed with
      | nominal found chosen finite residents =>
        cases allowed with
        | nominal other restriction fields =>
          cases Option.some.inj (other.symm.trans declared)
          simp [UsePermission.Allows, restricted] at restriction


structure StorageCell where
  activation : ActivationId
  type : Ty
  resident : PartialValue

def StorageCell.Typed (program : Program) (cell : StorageCell) (state : Initialization) : Prop :=
  FiniteLayout program.target program.data cell.type ∧
    cell.resident.Typed program cell.type state

/-- Preservation follows from the actual observation, independently of whether
checking has already established availability. -/
theorem PartialValue.Typed.read_sound {program : Program} {valueState : PartialValue} {type : Ty}
    {state : Initialization} (typed : valueState.Typed program type state) {value : Value}
    (read : valueState.read = some value) : ValueHasType program value type ∧ state.Ready := by
  induction typed using PartialValue.Typed.rec
    (motive_2 := fun partials types states _ => ∀ values,
      readPartialValues partials = some values →
      ValuesHaveTypes program values types ∧ InitializationsReady states) generalizing value with
  | hole => simp [PartialValue.read] at read
  | resident resident =>
    simp only [PartialValue.read, Option.some.injEq] at read
    subst value
    exact ⟨resident, .present⟩
  | tuple head tail headIH tailIH =>
    simp only [PartialValue.read, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨first, readFirst, rest, readRest, same⟩ := read
    subst value
    obtain ⟨firstTyped, firstReady⟩ := headIH readFirst
    obtain ⟨restTyped, restReady⟩ := tailIH rest readRest
    exact ⟨.tuple firstTyped restTyped, .fields (.cons firstReady restReady)⟩
  | nominal declared chosen finite residents ih =>
    simp only [PartialValue.read, Option.map_eq_some_iff] at read
    obtain ⟨values, read, same⟩ := read
    subst value
    obtain ⟨typed, ready⟩ := ih values read
    exact ⟨.nominal declared chosen finite typed, .fields ready⟩
  | nil =>
    rename_i values read
    simp only [readPartialValues, Option.some.injEq] at read
    subst values
    exact ⟨.nil, .nil⟩
  | cons head tail headIH tailIH =>
    rename_i values read
    simp only [readPartialValues, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨first, readFirst, rest, readRest, same⟩ := read
    subst values
    obtain ⟨firstTyped, firstReady⟩ := headIH readFirst
    obtain ⟨restTyped, restReady⟩ := tailIH rest readRest
    exact ⟨.cons firstTyped restTyped, .cons firstReady restReady⟩

def StorageCell.WellTyped (program : Program) (cell : StorageCell) : Prop :=
  ∃ state, cell.Typed program state

end Grounded
