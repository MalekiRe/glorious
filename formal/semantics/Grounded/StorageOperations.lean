import Grounded.PartialFields

/-! One path-based heap update contract for whole and partial transfers and
restoration. Empty paths are whole-owner operations, not a second API. -/
namespace Grounded

def takeStorage (program : Program) (heap : RuntimeHeap StorageCell) (identity : StorageId)
    (path : List FieldKey) : Option (Value × RuntimeHeap StorageCell) :=
  (heap.read identity).bind fun cell =>
    (cell.resident.selectFields program cell.type path).bind fun selected =>
      selected.read.bind fun value =>
        (cell.resident.writeFields program cell.type path .hole).bind fun updated =>
          (heap.write identity { cell with resident := updated }).map (value, ·)

def restoreStorage (program : Program) (heap : RuntimeHeap StorageCell) (identity : StorageId)
    (path : List FieldKey) (value : Value) : Option (RuntimeHeap StorageCell) :=
  (heap.read identity).bind fun cell =>
    (cell.resident.writeFields program cell.type path (.resident value)).bind fun updated =>
      heap.write identity { cell with resident := updated }

theorem takeStorage.progress {program : Program} {home : Module} {heap : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state selectedState : Initialization}
    {path : List FieldKey} {type : Ty}
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (checked : PathType program home cell.type path type)
    (selected : state.selectFields program cell.type path = some selectedState)
    (ready : selectedState.Ready) :
    ∃ value after updated afterState,
      state.writeFields program cell.type path .absent = some afterState ∧
      takeStorage program heap identity path = some (value, after) ∧
      ValueHasType program value type ∧
      heap.write identity { cell with resident := updated } = some after ∧
      StorageCell.Typed program { cell with resident := updated } afterState ∧
      after.read identity = some { cell with resident := updated } ∧
      takeStorage program after identity path = none ∧
      after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) := by
  obtain ⟨resident, actualState, stateSelected, residentSelected, residentTyped⟩ :=
    checked.select_partial typed.2
  have same := Option.some.inj (stateSelected.symm.trans selected)
  subst actualState
  obtain ⟨value, read, valueTyped⟩ := residentTyped.read ready
  obtain ⟨updated, afterState, stateWritten, written, updatedTyped, readback⟩ :=
    checked.restore_partial typed.1 typed.2 (.hole type)
  obtain ⟨after, stored⟩ := RuntimeHeap.write_exists found { cell with resident := updated }
  have newCell := RuntimeHeap.write_read stored
  exact ⟨value, after, updated, afterState, stateWritten,
    by simp [takeStorage, found, residentSelected, read, written, stored], valueTyped,
    stored, ⟨typed.1, updatedTyped⟩, newCell,
    by simp [takeStorage, newCell, readback, PartialValue.read], RuntimeHeap.write_next stored,
    fun _ different => RuntimeHeap.write_other stored different⟩

theorem restoreStorage.progress {program : Program} {home : Module} {heap : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state : Initialization}
    {path : List FieldKey} {type : Ty} {value : Value}
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (checked : PathType program home cell.type path type) (resident : ValueHasType program value type) :
    ∃ after updated afterState,
      state.writeFields program cell.type path .present = some afterState ∧
      restoreStorage program heap identity path value = some after ∧
      heap.write identity { cell with resident := updated } = some after ∧
      StorageCell.Typed program { cell with resident := updated } afterState ∧
      after.read identity = some { cell with resident := updated } ∧
      updated.selectFields program cell.type path = some (.resident value) ∧
      after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) := by
  obtain ⟨updated, afterState, stateWritten, written, updatedTyped, readback⟩ :=
    checked.restore_partial typed.1 typed.2 (.resident resident)
  obtain ⟨after, stored⟩ := RuntimeHeap.write_exists found { cell with resident := updated }
  exact ⟨after, updated, afterState, stateWritten,
    by simp [restoreStorage, found, written, stored], stored, ⟨typed.1, updatedTyped⟩,
    RuntimeHeap.write_read stored, readback, RuntimeHeap.write_next stored,
    fun _ different => RuntimeHeap.write_other stored different⟩

theorem takeStorage.preservation {program : Program} {home : Module} {heap after : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state selectedState : Initialization}
    {path : List FieldKey} {type : Ty} {value : Value}
    (store : heap.Typed (fun _ cell => cell.WellTyped program))
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (checked : PathType program home cell.type path type)
    (selected : state.selectFields program cell.type path = some selectedState)
    (ready : selectedState.Ready)
    (taken : takeStorage program heap identity path = some (value, after)) :
    after.Typed (fun _ cell => cell.WellTyped program) ∧ ValueHasType program value type := by
  obtain ⟨result, next, updated, afterState, _, step, resident, stored, afterTyped, _⟩ :=
    takeStorage.progress found typed checked selected ready
  have same := Option.some.inj (step.symm.trans taken)
  cases same
  exact ⟨store.write stored ⟨afterState, afterTyped⟩, resident⟩

theorem restoreStorage.preservation {program : Program} {home : Module} {heap after : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state : Initialization}
    {path : List FieldKey} {type : Ty} {value : Value}
    (store : heap.Typed (fun _ cell => cell.WellTyped program))
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (checked : PathType program home cell.type path type) (resident : ValueHasType program value type)
    (restored : restoreStorage program heap identity path value = some after) :
    after.Typed (fun _ cell => cell.WellTyped program) := by
  obtain ⟨next, updated, afterState, _, step, stored, afterTyped, _⟩ :=
    restoreStorage.progress found typed checked resident
  have same := Option.some.inj (step.symm.trans restored)
  subst next
  exact store.write stored ⟨afterState, afterTyped⟩

theorem takeStorage.retired {program : Program} {heap : RuntimeHeap StorageCell} {identity : StorageId}
    (retired : heap.Retired identity) (path : List FieldKey) : takeStorage program heap identity path = none := by
  simp [takeStorage, retired.2]

theorem restoreStorage.retired {program : Program} {heap : RuntimeHeap StorageCell} {identity : StorageId}
    (retired : heap.Retired identity) (path : List FieldKey) (value : Value) :
    restoreStorage program heap identity path value = none := by
  simp [restoreStorage, retired.2]





/-- Restoration changes only its selected physical path within the cell. -/
theorem restoreStorage.read_disjoint {program : Program} {home : Module}
    {before after : RuntimeHeap StorageCell} {identity : StorageId} {cell : StorageCell}
    {path observed : List FieldKey} {value : Value}
    (found : before.read identity = some cell)
    (apart : PathDisjoint program home cell.type path observed)
    (restored : restoreStorage program before identity path value = some after) :
    ((after.read identity).bind fun current =>
      (current.resident.selectFields program current.type observed).bind PartialValue.read) =
      (cell.resident.selectFields program cell.type observed).bind PartialValue.read := by
  simp only [restoreStorage, found, Option.bind_some, Option.bind_eq_some_iff] at restored
  obtain ⟨updated, written, stored⟩ := restored
  rw [RuntimeHeap.write_read stored]
  exact congrArg (fun selected => selected.bind PartialValue.read) (apart.write_frame written)

/-- Clearing a moved path preserves every disjoint observation in the same cell. -/
theorem takeStorage.read_disjoint {program : Program} {home : Module}
    {before after : RuntimeHeap StorageCell} {identity : StorageId} {cell : StorageCell}
    {path observed : List FieldKey} {value : Value}
    (found : before.read identity = some cell)
    (apart : PathDisjoint program home cell.type path observed)
    (taken : takeStorage program before identity path = some (value, after)) :
    ((after.read identity).bind fun current =>
      (current.resident.selectFields program current.type observed).bind PartialValue.read) =
      (cell.resident.selectFields program cell.type observed).bind PartialValue.read := by
  simp only [takeStorage, found, Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at taken
  obtain ⟨selected, selectedAt, owner, read, updated, written, heap, stored, same⟩ := taken
  cases same
  rw [RuntimeHeap.write_read stored]
  exact congrArg (fun selected => selected.bind PartialValue.read) (apart.write_frame written)

/-- The same cell supports a complete checked move/restoration sequence at any
field depth. The checking state records absent then present; no new storage
identity or activation is allocated, and no second transfer is admitted in the
intermediate hole. Every disjoint mask and read survives both transitions. -/
theorem takeStorage.restore {program : Program} {home : Module} {heap : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state selectedState : Initialization}
    {path : List FieldKey} {type : Ty} {replacement : Value}
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (checked : PathType program home cell.type path type)
    (selected : state.selectFields program cell.type path = some selectedState)
    (ready : selectedState.Ready) (replacementTyped : ValueHasType program replacement type) :
    ∃ value empty after movedState afterState updated,
      state.writeFields program cell.type path .absent = some movedState ∧
      movedState.writeFields program cell.type path .present = some afterState ∧
      takeStorage program heap identity path = some (value, empty) ∧
      ValueHasType program value type ∧
      takeStorage program empty identity path = none ∧
      restoreStorage program empty identity path replacement = some after ∧
      after.read identity = some { cell with resident := updated } ∧
      StorageCell.Typed program { cell with resident := updated } afterState ∧
      updated.selectFields program cell.type path = some (.resident replacement) ∧
      afterState.selectFields program cell.type path = some .present ∧
      after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) ∧
      (∀ observed, PathDisjoint program home cell.type path observed →
        movedState.selectFields program cell.type observed = state.selectFields program cell.type observed ∧
        afterState.selectFields program cell.type observed = state.selectFields program cell.type observed ∧
        ((empty.read identity).bind fun current =>
          (current.resident.selectFields program current.type observed).bind PartialValue.read) =
          (cell.resident.selectFields program cell.type observed).bind PartialValue.read ∧
        ((after.read identity).bind fun current =>
          (current.resident.selectFields program current.type observed).bind PartialValue.read) =
          (cell.resident.selectFields program cell.type observed).bind PartialValue.read) := by
  obtain ⟨value, empty, emptied, movedState, moved, taken, valueTyped, _, holeTyped,
    holeFound, noRetake, emptyNext, firstFrame⟩ :=
    takeStorage.progress found typed checked selected ready
  obtain ⟨after, updated, afterState, restoredState, restored, _, restoredTyped,
    restoredFound, readback, afterNext, lastFrame⟩ :=
    restoreStorage.progress holeFound holeTyped checked replacementTyped
  refine ⟨value, empty, after, movedState, afterState, updated, moved, restoredState,
    taken, valueTyped, noRetake, restored, restoredFound, restoredTyped, readback,
    Initialization.write_select restoredState, afterNext.trans emptyNext,
    (fun other different => (lastFrame other different).trans (firstFrame other different)), ?_⟩
  intro observed apart
  have intermediate := takeStorage.read_disjoint found apart taken
  refine ⟨apart.initialization_frame moved,
    (apart.initialization_frame restoredState).trans (apart.initialization_frame moved), intermediate, ?_⟩
  exact (restoreStorage.read_disjoint holeFound apart restored).trans
    (by simpa only [holeFound, Option.bind_some] using intermediate)


theorem takeStorage.history {program : Program} {heap after : RuntimeHeap StorageCell}
    {identity : StorageId} {path : List FieldKey} {value : Value}
    (taken : takeStorage program heap identity path = some (value, after)) :
    RuntimeHeap.History heap after := by
  simp only [takeStorage, Option.bind_eq_some_iff, Option.map_eq_some_iff] at taken
  obtain ⟨cell, _, selected, _, resident, _, updated, _, next, written, same⟩ := taken
  cases same
  exact .step (.write written) (.refl _)

theorem restoreStorage.history {program : Program} {heap after : RuntimeHeap StorageCell}
    {identity : StorageId} {path : List FieldKey} {value : Value}
    (restored : restoreStorage program heap identity path value = some after) :
    RuntimeHeap.History heap after := by
  simp only [restoreStorage, Option.bind_eq_some_iff] at restored
  obtain ⟨cell, _, updated, _, written⟩ := restored
  exact .step (.write written) (.refl _)


end Grounded
