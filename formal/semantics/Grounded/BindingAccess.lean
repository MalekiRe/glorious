import Grounded.BindingStorage

/-! Resolved lexical accesses use the same addressed cells and path operations
as allocation and scope retirement. Language permission is checked above here. -/
namespace Grounded

def BindingMap.read (bindings : BindingMap) (program : Program) (heap : RuntimeHeap StorageCell)
    (place : Place) : Option Value := do
  let identity ← lookup place.root bindings
  let cell ← heap.read identity
  let resident ← cell.resident.selectFields program cell.type place.fields
  resident.read

def BindingMap.take (bindings : BindingMap) (program : Program) (heap : RuntimeHeap StorageCell)
    (place : Place) : Option (Value × RuntimeHeap StorageCell) :=
  (lookup place.root bindings).bind fun identity => takeStorage program heap identity place.fields

def BindingMap.restore (bindings : BindingMap) (program : Program) (heap : RuntimeHeap StorageCell)
    (place : Place) (value : Value) : Option (RuntimeHeap StorageCell) :=
  (lookup place.root bindings).bind fun identity => restoreStorage program heap identity place.fields value

variable {program : Program} {home : Module} {heap : RuntimeHeap StorageCell} {activation : ActivationId}
    {bindings : BindingMap} {context : List (BindingId × BindingState)}
    {place : Place} {state : BindingState} {type : Ty}

theorem BindingMap.read.progress (typed : BindingMap.Typed program heap activation bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {selectedState : Initialization}
    (selected : state.initialization.selectFields program state.slot.type place.fields = some selectedState)
    (ready : selectedState.Ready) :
    ∃ value, bindings.read program heap place = some value ∧ ValueHasType program value type := by
  obtain ⟨identity, cell, mapped, found, _, declared, resident, _⟩ := typed.lookup resolved
  have path : PathType program home cell.type place.fields type := by simpa only [declared] using checked
  obtain ⟨selectedResident, actualState, stateFound, partialFound, partialTyped⟩ := path.select_partial resident.2
  rw [declared, selected] at stateFound
  cases stateFound
  obtain ⟨value, read, valueTyped⟩ := partialTyped.read ready
  exact ⟨value, by simp [BindingMap.read, mapped, found, partialFound, read], valueTyped⟩

/-- A move changes the checking state and the actual resident together. The
same binding map survives; every other storage identity is framed. -/
theorem BindingMap.take.progress (typed : BindingMap.Typed program heap activation bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {selectedState : Initialization}
    (selected : state.initialization.selectFields program state.slot.type place.fields = some selectedState)
    (ready : selectedState.Ready) :
    ∃ identity value after nextState nextContext,
      lookup place.root bindings = some identity ∧
      state.initialization.writeFields program state.slot.type place.fields .absent = some nextState ∧
      replaceBinding place.root { state with initialization := nextState } context = some nextContext ∧
      bindings.take program heap place = some (value, after) ∧
      ValueHasType program value type ∧
      BindingMap.Typed program after activation bindings nextContext ∧
      bindings.take program after place = none ∧ after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) ∧
      (∀ (caller : AddressedScope) states, BindingMap.Typed program heap caller.activation caller.bindings states →
        caller.activation ≠ activation → BindingMap.Typed program after caller.activation caller.bindings states) := by
  obtain ⟨identity, cell, mapped, found, owner, declared, resident, _⟩ := typed.lookup resolved
  have path : PathType program home cell.type place.fields type := by simpa only [declared] using checked
  have selection : state.initialization.selectFields program cell.type place.fields = some selectedState := by
    simpa only [declared] using selected
  obtain ⟨value, after, updated, nextState, stateWritten, taken, valueTyped, written, updatedTyped,
    _, noRetake, next, framed⟩ := takeStorage.progress found resident path selection ready
  obtain ⟨nextContext, replaced, afterTyped⟩ := typed.write resolved mapped written owner declared updatedTyped
  exact ⟨identity, value, after, nextState, nextContext, mapped,
    by simpa only [declared] using stateWritten, replaced,
    by simp [BindingMap.take, mapped, taken], valueTyped, afterTyped,
    by simp [BindingMap.take, mapped, noRetake], next, framed,
    fun _ _ callerTyped different => callerTyped.frame_other_activation found
      (by simpa only [owner] using different) framed⟩

/-- Restoration updates a live slot, including a partially absent aggregate;
it does not allocate a replacement identity or revive retired storage. -/
theorem BindingMap.restore.progress (typed : BindingMap.Typed program heap activation bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {value : Value} (valueTyped : ValueHasType program value type) :
    ∃ identity after nextState nextContext,
      lookup place.root bindings = some identity ∧
      state.initialization.writeFields program state.slot.type place.fields .present = some nextState ∧
      replaceBinding place.root { state with initialization := nextState } context = some nextContext ∧
      bindings.restore program heap place value = some after ∧
      BindingMap.Typed program after activation bindings nextContext ∧
      bindings.read program after place = some value ∧ after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) ∧
      (state.initialization.Ready → nextState.Ready) ∧
      (∀ (caller : AddressedScope) states, BindingMap.Typed program heap caller.activation caller.bindings states →
        caller.activation ≠ activation → BindingMap.Typed program after caller.activation caller.bindings states) := by
  obtain ⟨identity, cell, mapped, found, owner, declared, resident, _⟩ := typed.lookup resolved
  have path : PathType program home cell.type place.fields type := by simpa only [declared] using checked
  obtain ⟨after, updated, nextState, stateWritten, restored, written, updatedTyped,
    updatedFound, readback, next, framed⟩ := restoreStorage.progress found resident path valueTyped
  obtain ⟨nextContext, replaced, afterTyped⟩ := typed.write resolved mapped written owner declared updatedTyped
  exact ⟨identity, after, nextState, nextContext, mapped,
    by simpa only [declared] using stateWritten, replaced,
    by simp [BindingMap.restore, mapped, restored], afterTyped,
    by simp [BindingMap.read, mapped, updatedFound, readback, PartialValue.read], next, framed,
    (fun ready => Initialization.write_ready ready .present stateWritten),
    fun _ _ callerTyped different => callerTyped.frame_other_activation found
      (by simpa only [owner] using different) framed⟩

def AddressedEnvironment.read (current : AddressedEnvironment) (program : Program) (place : Place) : Option Value :=
  current.bindings.read program current.heap place

def AddressedEnvironment.take (current : AddressedEnvironment) (program : Program) (place : Place) :
    Option (Value × AddressedEnvironment) :=
  (current.bindings.take program current.heap place).map fun result =>
    (result.1, { current with heap := result.2 })

def AddressedEnvironment.write (current : AddressedEnvironment) (program : Program) (place : Place) (value : Value) :
    Option AddressedEnvironment :=
  (current.bindings.restore program current.heap place value).map fun heap => { current with heap := heap }

theorem AddressedEnvironment.read.progress {current : AddressedEnvironment}
    (typed : BindingMap.Typed program current.heap current.activation current.bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {selectedState : Initialization}
    (selected : state.initialization.selectFields program state.slot.type place.fields = some selectedState)
    (ready : selectedState.Ready) :
    ∃ value, current.read program place = some value ∧ ValueHasType program value type :=
  BindingMap.read.progress typed resolved checked selected ready

theorem AddressedEnvironment.take.progress {current : AddressedEnvironment}
    (typed : BindingMap.Typed program current.heap current.activation current.bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {selectedState : Initialization}
    (selected : state.initialization.selectFields program state.slot.type place.fields = some selectedState)
    (ready : selectedState.Ready) :
    ∃ value after nextState nextContext,
      current.take program place = some (value, after) ∧ ValueHasType program value type ∧
      state.initialization.writeFields program state.slot.type place.fields .absent = some nextState ∧
      replaceBinding place.root { state with initialization := nextState } context = some nextContext ∧
      BindingMap.Typed program after.heap after.activation after.bindings nextContext ∧
      after.take program place = none ∧ after.scope = current.scope ∧ after.supply = current.supply ∧
      after.heap.next = current.heap.next ∧
      (∀ (caller : AddressedScope) states, BindingMap.Typed program current.heap caller.activation caller.bindings states →
        caller.activation ≠ current.activation → BindingMap.Typed program after.heap caller.activation caller.bindings states) := by
  obtain ⟨identity, value, heap, nextState, nextContext, _, stateWritten, replaced,
    taken, resident, afterTyped, noRetake, next, _, retained⟩ :=
    BindingMap.take.progress typed resolved checked selected ready
  exact ⟨value, { current with heap := heap }, nextState, nextContext,
    by simp [AddressedEnvironment.take, taken], resident, stateWritten, replaced, afterTyped,
    by simp [AddressedEnvironment.take, noRetake], rfl, rfl, next, retained⟩

theorem AddressedEnvironment.write.progress {current : AddressedEnvironment}
    (typed : BindingMap.Typed program current.heap current.activation current.bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {value : Value} (resident : ValueHasType program value type) :
    ∃ after nextState nextContext,
      current.write program place value = some after ∧
      state.initialization.writeFields program state.slot.type place.fields .present = some nextState ∧
      replaceBinding place.root { state with initialization := nextState } context = some nextContext ∧
      BindingMap.Typed program after.heap after.activation after.bindings nextContext ∧
      after.read program place = some value ∧ after.scope = current.scope ∧ after.supply = current.supply ∧
      after.heap.next = current.heap.next ∧ (state.initialization.Ready → nextState.Ready) ∧
      (∀ (caller : AddressedScope) states, BindingMap.Typed program current.heap caller.activation caller.bindings states →
        caller.activation ≠ current.activation → BindingMap.Typed program after.heap caller.activation caller.bindings states) := by
  obtain ⟨identity, heap, nextState, nextContext, _, stateWritten, replaced,
    written, afterTyped, readback, next, _, initialized, retained⟩ :=
    BindingMap.restore.progress typed resolved checked resident
  exact ⟨{ current with heap := heap }, nextState, nextContext,
    by simp [AddressedEnvironment.write, written], stateWritten, replaced, afterTyped,
    readback, rfl, rfl, next, initialized, retained⟩


end Grounded
