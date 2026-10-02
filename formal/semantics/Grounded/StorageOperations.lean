import Grounded.PartialFields

/-! One path-based heap update contract for whole and partial transfers and
restoration. Empty paths are whole-owner operations, not a second API. -/
namespace Grounded

def StorageAddress.read (program : Program) (heap : RuntimeHeap StorageCell)
    (address : StorageAddress) : Option Value := do
  let cell ← heap.read address.root
  let resident ← cell.resident.selectFields program cell.type address.fields
  resident.read

def StorageAddress.take (program : Program) (heap : RuntimeHeap StorageCell)
    (address : StorageAddress) : Option (Value × RuntimeHeap StorageCell) :=
  (heap.read address.root).bind fun cell =>
    (cell.resident.selectFields program cell.type address.fields).bind fun selected =>
      selected.read.bind fun value =>
        (cell.resident.writeFields program cell.type address.fields .hole).bind fun updated =>
          (heap.write address.root { cell with resident := updated }).map (value, ·)

def StorageAddress.restore (program : Program) (heap : RuntimeHeap StorageCell)
    (address : StorageAddress) (value : Value) : Option (RuntimeHeap StorageCell) :=
  (heap.read address.root).bind fun cell =>
    (cell.resident.writeFields program cell.type address.fields (.resident value)).bind fun updated =>
      heap.write address.root { cell with resident := updated }

/-- A move returns precisely the resident selected before clearing the path. -/
theorem StorageAddress.take.read_before {program : Program} {before after : RuntimeHeap StorageCell}
    {address : StorageAddress} {value : Value}
    (taken : address.take program before = some (value, after)) :
    address.read program before = some value := by
  simp only [StorageAddress.take, Option.bind_eq_some_iff, Option.map_eq_some_iff] at taken
  obtain ⟨cell, found, selected, selectedAt, owner, read, updated, _, heap, _, same⟩ := taken
  cases same
  simp [StorageAddress.read, found, selectedAt, read]


/-- Exact address typing comes from the current cell and the shared projection
judgment. It grants neither initialization nor permission to access a loan. -/
inductive StorageAddress.Typed (program : Program) (heap : RuntimeHeap StorageCell) :
    StorageAddress → Ty → Prop where
  | intro {identity : StorageId} {fields : List FieldKey} {home : Module} {cell : StorageCell} {type : Ty}
      (found : heap.read identity = some cell)
      (path : PathType program home cell.type fields type) :
      StorageAddress.Typed program heap ⟨identity, fields⟩ type

theorem StorageAddress.Typed.path {program : Program} {heap : RuntimeHeap StorageCell}
    {address : StorageAddress} {type : Ty} {cell : StorageCell}
    (checked : address.Typed program heap type) (found : heap.read address.root = some cell) :
    ∃ home, PathType program home cell.type address.fields type := by
  cases checked with
  | intro original path =>
    cases Option.some.inj (original.symm.trans found)
    exact ⟨_, path⟩

theorem StorageAddress.Typed.unique {program : Program} {heap : RuntimeHeap StorageCell}
    {address : StorageAddress} {left right : Ty}
    (first : address.Typed program heap left) (second : address.Typed program heap right) : left = right := by
  cases first with
  | intro found path =>
    obtain ⟨home, other⟩ := second.path found
    exact path.result_unique other

/-- Address separation uses the existing checked path geometry in the actual
pre-state cell. Distinct lexical names alone are not evidence of separation. -/
inductive StorageAddress.Disjoint (program : Program) (heap : RuntimeHeap StorageCell) :
    StorageAddress → StorageAddress → Prop where
  | roots {left right : StorageAddress} (different : left.root ≠ right.root) :
      Disjoint program heap left right
  | fields {identity : StorageId} {left right : List FieldKey} {home : Module} {cell : StorageCell}
      (found : heap.read identity = some cell)
      (apart : PathDisjoint program home cell.type left right) :
      Disjoint program heap ⟨identity, left⟩ ⟨identity, right⟩


theorem StorageAddress.read.progress {program : Program} {heap : RuntimeHeap StorageCell}
    {address : StorageAddress} {cell : StorageCell} {state selectedState : Initialization} {type : Ty}
    (found : heap.read address.root = some cell) (resident : cell.Typed program state)
    (checked : address.Typed program heap type)
    (selected : state.selectFields program cell.type address.fields = some selectedState)
    (ready : selectedState.Ready) :
    ∃ value, address.read program heap = some value ∧ ValueHasType program value type := by
  obtain ⟨home, path⟩ := checked.path found
  obtain ⟨part, mask, maskFound, partialFound, partialTyped⟩ := path.select_partial resident.2
  cases Option.some.inj (maskFound.symm.trans selected)
  obtain ⟨value, read, typed⟩ := partialTyped.read ready
  exact ⟨value, by simp [StorageAddress.read, found, partialFound, read], typed⟩


theorem StorageAddress.take.progress {program : Program} {heap : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state selectedState : Initialization}
    {path : List FieldKey} {type : Ty}
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (checked : StorageAddress.Typed program heap ⟨identity, path⟩ type)
    (selected : state.selectFields program cell.type path = some selectedState)
    (ready : selectedState.Ready) :
    ∃ value after updated afterState,
      state.writeFields program cell.type path .absent = some afterState ∧
      StorageAddress.take program heap ⟨identity, path⟩ = some (value, after) ∧
      ValueHasType program value type ∧
      heap.write identity { cell with resident := updated } = some after ∧
      StorageCell.Typed program { cell with resident := updated } afterState ∧
      after.read identity = some { cell with resident := updated } ∧
      StorageAddress.take program after ⟨identity, path⟩ = none ∧
      after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) := by
  obtain ⟨home, checked⟩ := checked.path found
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
    by simp [StorageAddress.take, found, residentSelected, read, written, stored], valueTyped,
    stored, ⟨typed.1, updatedTyped⟩, newCell,
    by simp [StorageAddress.take, newCell, readback, PartialValue.read], RuntimeHeap.write_next stored,
    fun _ different => RuntimeHeap.write_other stored different⟩

theorem StorageAddress.restore.progress {program : Program} {heap : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state : Initialization}
    {path : List FieldKey} {type : Ty} {value : Value}
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (checked : StorageAddress.Typed program heap ⟨identity, path⟩ type) (resident : ValueHasType program value type) :
    ∃ after updated afterState,
      state.writeFields program cell.type path .present = some afterState ∧
      StorageAddress.restore program heap ⟨identity, path⟩ value = some after ∧
      heap.write identity { cell with resident := updated } = some after ∧
      StorageCell.Typed program { cell with resident := updated } afterState ∧
      after.read identity = some { cell with resident := updated } ∧
      updated.selectFields program cell.type path = some (.resident value) ∧
      after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) := by
  obtain ⟨home, checked⟩ := checked.path found
  obtain ⟨updated, afterState, stateWritten, written, updatedTyped, readback⟩ :=
    checked.restore_partial typed.1 typed.2 (.resident resident)
  obtain ⟨after, stored⟩ := RuntimeHeap.write_exists found { cell with resident := updated }
  exact ⟨after, updated, afterState, stateWritten,
    by simp [StorageAddress.restore, found, written, stored], stored, ⟨typed.1, updatedTyped⟩,
    RuntimeHeap.write_read stored, readback, RuntimeHeap.write_next stored,
    fun _ different => RuntimeHeap.write_other stored different⟩

theorem StorageAddress.take.preservation {program : Program} {home : Module} {heap after : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state selectedState : Initialization}
    {path : List FieldKey} {type : Ty} {value : Value}
    (store : heap.Typed (fun _ cell => cell.WellTyped program))
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (checked : PathType program home cell.type path type)
    (selected : state.selectFields program cell.type path = some selectedState)
    (ready : selectedState.Ready)
    (taken : StorageAddress.take program heap ⟨identity, path⟩ = some (value, after)) :
    after.Typed (fun _ cell => cell.WellTyped program) ∧ ValueHasType program value type := by
  obtain ⟨result, next, updated, afterState, _, step, resident, stored, afterTyped, _⟩ :=
    StorageAddress.take.progress found typed (.intro found checked) selected ready
  have same := Option.some.inj (step.symm.trans taken)
  cases same
  exact ⟨store.write stored ⟨afterState, afterTyped⟩, resident⟩

theorem StorageAddress.restore.preservation {program : Program} {home : Module} {heap after : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state : Initialization}
    {path : List FieldKey} {type : Ty} {value : Value}
    (store : heap.Typed (fun _ cell => cell.WellTyped program))
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (checked : PathType program home cell.type path type) (resident : ValueHasType program value type)
    (restored : StorageAddress.restore program heap ⟨identity, path⟩ value = some after) :
    after.Typed (fun _ cell => cell.WellTyped program) := by
  obtain ⟨next, updated, afterState, _, step, stored, afterTyped, _⟩ :=
    StorageAddress.restore.progress found typed (.intro found checked) resident
  have same := Option.some.inj (step.symm.trans restored)
  subst next
  exact store.write stored ⟨afterState, afterTyped⟩

theorem StorageAddress.take.retired {program : Program} {heap : RuntimeHeap StorageCell} {identity : StorageId}
    (retired : heap.Retired identity) (path : List FieldKey) : StorageAddress.take program heap ⟨identity, path⟩ = none := by
  simp [StorageAddress.take, retired.2]

theorem StorageAddress.restore.retired {program : Program} {heap : RuntimeHeap StorageCell} {identity : StorageId}
    (retired : heap.Retired identity) (path : List FieldKey) (value : Value) :
    StorageAddress.restore program heap ⟨identity, path⟩ value = none := by
  simp [StorageAddress.restore, retired.2]





/-- Restoration changes only its selected physical path within the cell. -/
theorem StorageAddress.restore.read_disjoint {program : Program} {home : Module}
    {before after : RuntimeHeap StorageCell} {identity : StorageId} {cell : StorageCell}
    {path observed : List FieldKey} {value : Value}
    (found : before.read identity = some cell)
    (apart : PathDisjoint program home cell.type path observed)
    (restored : StorageAddress.restore program before ⟨identity, path⟩ value = some after) :
    ((after.read identity).bind fun current =>
      (current.resident.selectFields program current.type observed).bind PartialValue.read) =
      (cell.resident.selectFields program cell.type observed).bind PartialValue.read := by
  simp only [StorageAddress.restore, found, Option.bind_some, Option.bind_eq_some_iff] at restored
  obtain ⟨updated, written, stored⟩ := restored
  rw [RuntimeHeap.write_read stored]
  exact congrArg (fun selected => selected.bind PartialValue.read) (apart.write_frame written)

/-- Clearing a moved path preserves every disjoint observation in the same cell. -/
theorem StorageAddress.take.read_disjoint {program : Program} {home : Module}
    {before after : RuntimeHeap StorageCell} {identity : StorageId} {cell : StorageCell}
    {path observed : List FieldKey} {value : Value}
    (found : before.read identity = some cell)
    (apart : PathDisjoint program home cell.type path observed)
    (taken : StorageAddress.take program before ⟨identity, path⟩ = some (value, after)) :
    ((after.read identity).bind fun current =>
      (current.resident.selectFields program current.type observed).bind PartialValue.read) =
      (cell.resident.selectFields program cell.type observed).bind PartialValue.read := by
  simp only [StorageAddress.take, found, Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at taken
  obtain ⟨selected, selectedAt, owner, read, updated, written, heap, stored, same⟩ := taken
  cases same
  rw [RuntimeHeap.write_read stored]
  exact congrArg (fun selected => selected.bind PartialValue.read) (apart.write_frame written)

/-- Restoration preserves every pre-state-separated address observation. -/
theorem StorageAddress.restore.read_frame {program : Program}
    {before after : RuntimeHeap StorageCell} {address observed : StorageAddress} {value : Value}
    (apart : address.Disjoint program before observed)
    (restored : address.restore program before value = some after) :
    observed.read program after = observed.read program before := by
  cases apart with
  | roots different =>
    simp only [StorageAddress.restore, Option.bind_eq_some_iff] at restored
    obtain ⟨cell, _, updated, _, written⟩ := restored
    simp only [StorageAddress.read, RuntimeHeap.write_other written (Ne.symm different)]
  | fields found separated =>
    simpa [StorageAddress.read, found] using
      StorageAddress.restore.read_disjoint found separated restored

/-- Moving a field preserves every pre-state-separated address observation. -/
theorem StorageAddress.take.read_frame {program : Program}
    {before after : RuntimeHeap StorageCell} {address observed : StorageAddress} {value : Value}
    (apart : address.Disjoint program before observed)
    (taken : address.take program before = some (value, after)) :
    observed.read program after = observed.read program before := by
  cases apart with
  | roots different =>
    simp only [StorageAddress.take, Option.bind_eq_some_iff, Option.map_eq_some_iff] at taken
    obtain ⟨cell, _, selected, _, owner, _, updated, _, heap, written, same⟩ := taken
    cases same
    simp only [StorageAddress.read, RuntimeHeap.write_other written (Ne.symm different)]
  | fields found separated =>
    simpa [StorageAddress.read, found] using
      StorageAddress.take.read_disjoint found separated taken


/-- The same cell supports a complete checked move/restoration sequence at any
field depth. The checking state records absent then present; no new storage
identity or activation is allocated, and no second transfer is admitted in the
intermediate hole. Every disjoint mask and read survives both transitions. -/
theorem StorageAddress.take.restore {program : Program} {home : Module} {heap : RuntimeHeap StorageCell}
    {identity : StorageId} {cell : StorageCell} {state selectedState : Initialization}
    {path : List FieldKey} {type : Ty} {replacement : Value}
    (found : heap.read identity = some cell) (typed : cell.Typed program state)
    (checked : PathType program home cell.type path type)
    (selected : state.selectFields program cell.type path = some selectedState)
    (ready : selectedState.Ready) (replacementTyped : ValueHasType program replacement type) :
    ∃ value empty after movedState afterState updated,
      state.writeFields program cell.type path .absent = some movedState ∧
      movedState.writeFields program cell.type path .present = some afterState ∧
      StorageAddress.take program heap ⟨identity, path⟩ = some (value, empty) ∧
      ValueHasType program value type ∧
      StorageAddress.take program empty ⟨identity, path⟩ = none ∧
      StorageAddress.restore program empty ⟨identity, path⟩ replacement = some after ∧
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
    StorageAddress.take.progress found typed (.intro found checked) selected ready
  obtain ⟨after, updated, afterState, restoredState, restored, _, restoredTyped,
    restoredFound, readback, afterNext, lastFrame⟩ :=
    StorageAddress.restore.progress holeFound holeTyped (.intro holeFound checked) replacementTyped
  refine ⟨value, empty, after, movedState, afterState, updated, moved, restoredState,
    taken, valueTyped, noRetake, restored, restoredFound, restoredTyped, readback,
    Initialization.write_select restoredState, afterNext.trans emptyNext,
    (fun other different => (lastFrame other different).trans (firstFrame other different)), ?_⟩
  intro observed apart
  have intermediate := StorageAddress.take.read_disjoint found apart taken
  refine ⟨apart.initialization_frame moved,
    (apart.initialization_frame restoredState).trans (apart.initialization_frame moved), intermediate, ?_⟩
  exact (StorageAddress.restore.read_disjoint holeFound apart restored).trans
    (by simpa only [holeFound, Option.bind_some] using intermediate)


theorem StorageAddress.take.history {program : Program} {heap after : RuntimeHeap StorageCell}
    {identity : StorageId} {path : List FieldKey} {value : Value}
    (taken : StorageAddress.take program heap ⟨identity, path⟩ = some (value, after)) :
    RuntimeHeap.History heap after := by
  simp only [StorageAddress.take, Option.bind_eq_some_iff, Option.map_eq_some_iff] at taken
  obtain ⟨cell, _, selected, _, resident, _, updated, _, next, written, same⟩ := taken
  cases same
  exact .step (.write written) (.refl _)

theorem StorageAddress.restore.history {program : Program} {heap after : RuntimeHeap StorageCell}
    {identity : StorageId} {path : List FieldKey} {value : Value}
    (restored : StorageAddress.restore program heap ⟨identity, path⟩ value = some after) :
    RuntimeHeap.History heap after := by
  simp only [StorageAddress.restore, Option.bind_eq_some_iff] at restored
  obtain ⟨cell, _, updated, _, written⟩ := restored
  exact .step (.write written) (.refl _)


/-- A resident update preserves the cell's allocation owner and declared type. -/
theorem RuntimeHeap.write_resident_identity {before after : RuntimeHeap StorageCell}
    {identity observed : StorageId} {cell result : StorageCell} {resident : PartialValue}
    (original : before.read identity = some cell)
    (written : before.write identity { cell with resident := resident } = some after)
    (found : after.read observed = some result) :
    ∃ old, before.read observed = some old ∧ result.activation = old.activation ∧ result.type = old.type := by
  by_cases same : observed = identity
  · subst observed
    cases Option.some.inj ((RuntimeHeap.write_read written).symm.trans found)
    exact ⟨cell, original, rfl, rfl⟩
  · rw [RuntimeHeap.write_other written same] at found
    exact ⟨result, found, rfl, rfl⟩

theorem StorageAddress.take.identity {program : Program} {heap after : RuntimeHeap StorageCell}
    {identity observed : StorageId} {path : List FieldKey} {value : Value} {result : StorageCell}
    (taken : StorageAddress.take program heap ⟨identity, path⟩ = some (value, after))
    (found : after.read observed = some result) :
    ∃ old, heap.read observed = some old ∧ result.activation = old.activation ∧ result.type = old.type := by
  simp only [StorageAddress.take, Option.bind_eq_some_iff, Option.map_eq_some_iff] at taken
  obtain ⟨cell, original, selected, _, resident, _, updated, _, next, written, same⟩ := taken
  cases same
  exact RuntimeHeap.write_resident_identity original written found

theorem StorageAddress.restore.identity {program : Program} {heap after : RuntimeHeap StorageCell}
    {identity observed : StorageId} {path : List FieldKey} {value : Value} {result : StorageCell}
    (restored : StorageAddress.restore program heap ⟨identity, path⟩ value = some after)
    (found : after.read observed = some result) :
    ∃ old, heap.read observed = some old ∧ result.activation = old.activation ∧ result.type = old.type := by
  simp only [StorageAddress.restore, Option.bind_eq_some_iff] at restored
  obtain ⟨cell, original, updated, _, written⟩ := restored
  exact RuntimeHeap.write_resident_identity original written found


/-- Moving retains the same live cell, activation and declared type, with a
concrete hole at the moved path; failed rereading is not evidence of retirement. -/
theorem StorageAddress.take.hole {program : Program} {before after : RuntimeHeap StorageCell}
    {address : StorageAddress} {value : Value}
    (taken : address.take program before = some (value, after)) :
    ∃ old next, before.read address.root = some old ∧ after.read address.root = some next ∧
      next.activation = old.activation ∧ next.type = old.type ∧
      next.resident.selectFields program next.type address.fields = some .hole := by
  simp only [StorageAddress.take, Option.bind_eq_some_iff, Option.map_eq_some_iff] at taken
  obtain ⟨cell, original, selected, _, resident, _, updated, changed, heap, written, same⟩ := taken
  cases same
  exact ⟨cell, { cell with resident := updated }, original, RuntimeHeap.write_read written,
    rfl, rfl, PartialValue.write_select changed⟩

end Grounded
