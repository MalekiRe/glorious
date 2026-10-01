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

structure StorageCell where
  activation : ActivationId
  type : Ty
  resident : PartialValue

def StorageCell.Typed (program : Program) (cell : StorageCell) (state : Initialization) : Prop :=
  FiniteLayout program.target program.data cell.type ∧
    cell.resident.Typed program cell.type state

/-- Transfers the resident, not the cell. Its address, declared type, and
activation survive; the hole cannot subsequently be read. -/
def takeStorage (heap : RuntimeHeap StorageCell) (identity : StorageId) :
    Option (Value × RuntimeHeap StorageCell) :=
  (heap.read identity).bind fun cell =>
    cell.resident.read.bind fun value =>
      (heap.write identity { cell with resident := .hole }).map (value, ·)

/-- Restoration writes the same live cell, including when its resident is a
hole. Retired storage is never treated as an initialization hole. -/
def restoreStorage (heap : RuntimeHeap StorageCell) (identity : StorageId) (value : Value) :
    Option (RuntimeHeap StorageCell) :=
  (heap.read identity).bind fun cell =>
    heap.write identity { cell with resident := .resident value }

theorem takeStorage.progress {program : Program} {heap : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state : Initialization}
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (ready : state.Ready) :
    ∃ value after, takeStorage heap identity = some (value, after) ∧
      ValueHasType program value cell.type ∧
      after.read identity = some { cell with resident := .hole } ∧
      after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) := by
  obtain ⟨value, read, valueTyped⟩ := PartialValue.Typed.read typed.2 ready
  obtain ⟨after, written⟩ := RuntimeHeap.write_exists found { cell with resident := .hole }
  exact ⟨value, after, by simp [takeStorage, found, read, written], valueTyped,
    RuntimeHeap.write_read written, RuntimeHeap.write_next written,
    fun _ different => RuntimeHeap.write_other written different⟩

theorem restoreStorage.progress {program : Program} {heap : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {value : Value}
    (found : heap.read identity = some cell) (resident : ValueHasType program value cell.type) :
    ∃ after, restoreStorage heap identity value = some after ∧
      after.read identity = some { cell with resident := .resident value } ∧
      StorageCell.Typed program { cell with resident := .resident value } .present ∧
      after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) := by
  obtain ⟨after, written⟩ := RuntimeHeap.write_exists found { cell with resident := .resident value }
  exact ⟨after, by simp [restoreStorage, found, written], RuntimeHeap.write_read written,
    ⟨resident.finite, .resident resident⟩, RuntimeHeap.write_next written,
    fun _ different => RuntimeHeap.write_other written different⟩


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

theorem takeStorage.effect {heap after : RuntimeHeap StorageCell} {identity : StorageId} {value : Value}
    (taken : takeStorage heap identity = some (value, after)) :
    ∃ cell, heap.read identity = some cell ∧ cell.resident.read = some value ∧
      heap.write identity { cell with resident := .hole } = some after := by
  simp only [takeStorage, Option.bind_eq_some_iff, Option.map_eq_some_iff] at taken
  obtain ⟨cell, found, resident, read, result, written, same⟩ := taken
  cases same
  exact ⟨cell, found, read, written⟩

theorem restoreStorage.effect {heap after : RuntimeHeap StorageCell} {identity : StorageId} {value : Value}
    (restored : restoreStorage heap identity value = some after) :
    ∃ cell, heap.read identity = some cell ∧
      heap.write identity { cell with resident := .resident value } = some after := by
  simpa only [restoreStorage, Option.bind_eq_some_iff] using restored

theorem takeStorage.preservation {program : Program} {heap after : RuntimeHeap StorageCell}
    {identity : StorageId} {value : Value}
    (store : heap.Typed (fun _ cell => cell.WellTyped program))
    (taken : takeStorage heap identity = some (value, after)) :
    after.Typed (fun _ cell => cell.WellTyped program) ∧
      takeStorage after identity = none ∧
      ∃ cell, heap.read identity = some cell ∧ ValueHasType program value cell.type ∧
        after.read identity = some { cell with resident := .hole } := by
  obtain ⟨cell, found, read, written⟩ := takeStorage.effect taken
  obtain ⟨state, resident⟩ := store _ _ found
  have typed := (PartialValue.Typed.read_sound resident.2 read).1
  have hole := RuntimeHeap.write_read written
  exact ⟨store.write written ⟨.absent, resident.1, .hole cell.type⟩,
    by simp [takeStorage, hole, PartialValue.read], cell, found, typed, hole⟩

theorem restoreStorage.preservation {program : Program} {heap after : RuntimeHeap StorageCell}
    {identity : StorageId} {value : Value}
    (store : heap.Typed (fun _ cell => cell.WellTyped program))
    (resident : ∀ cell, heap.read identity = some cell → ValueHasType program value cell.type)
    (restored : restoreStorage heap identity value = some after) :
    after.Typed (fun _ cell => cell.WellTyped program) := by
  obtain ⟨cell, found, written⟩ := restoreStorage.effect restored
  exact store.write written ⟨.present, (resident cell found).finite, .resident (resident cell found)⟩



/-- Taking then restoring any correctly typed replacement leaves the same live
storage identity and activation. All unrelated cells are framed through both
operations; the resident cannot be taken a second time before restoration. -/
theorem takeStorage.restore {program : Program} {heap : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state : Initialization} {replacement : Value}
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (ready : state.Ready) (replacementTyped : ValueHasType program replacement cell.type) :
    ∃ value empty restored,
      takeStorage heap identity = some (value, empty) ∧
      ValueHasType program value cell.type ∧
      empty.read identity = some { cell with resident := .hole } ∧
      takeStorage empty identity = none ∧
      restoreStorage empty identity replacement = some restored ∧
      restored.read identity = some { cell with resident := .resident replacement } ∧
      restored.next = heap.next ∧
      (∀ other, other ≠ identity → restored.read other = heap.read other) := by
  obtain ⟨value, empty, taken, valueTyped, hole, emptyNext, firstFrame⟩ :=
    takeStorage.progress found typed ready
  obtain ⟨restored, written, full, _, restoredNext, lastFrame⟩ :=
    restoreStorage.progress hole replacementTyped
  exact ⟨value, empty, restored, taken, valueTyped, hole,
    by simp [takeStorage, hole, PartialValue.read], written, full,
    restoredNext.trans emptyNext,
    fun other different => (lastFrame other different).trans (firstFrame other different)⟩

theorem takeStorage.retired {heap : RuntimeHeap StorageCell} {identity : StorageId}
    (retired : heap.Retired identity) : takeStorage heap identity = none := by
  simp [takeStorage, retired.2]

theorem restoreStorage.retired {heap : RuntimeHeap StorageCell} {identity : StorageId}
    (retired : heap.Retired identity) (value : Value) : restoreStorage heap identity value = none := by
  simp [restoreStorage, retired.2]


end Grounded
