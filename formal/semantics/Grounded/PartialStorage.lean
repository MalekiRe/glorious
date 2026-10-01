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

/-- A scope may retire an empty shell without assigning discard permission to
its type. Otherwise this fragment requires ordinary structural MayDiscard. -/
def Initialization.Disposable (data : DataDeclarations) (type : Ty) (state : Initialization) : Prop :=
  state.Empty ∨ UsePermitted data .discard type

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
