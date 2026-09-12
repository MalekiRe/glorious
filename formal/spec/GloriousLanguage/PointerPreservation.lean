import GloriousLanguage.RelocationPreservation

/-! Pointer representation preservation through the actual memory producers,
storage writes, retirement and snapshot relocation. Allocation provenance does
not supply access permission, and stale generations are never refreshed. -/
namespace Glorious.Language

theorem RawPointer.Origin.weaken {pointer : RawPointer} {before after : World}
    (origin : pointer.Origin before)
    (roots : ∀ id root, before.roots.get id = some root → after.roots.get id = some root) :
    pointer.Origin after := by
  intro id allocation
  obtain ⟨root,found,address,offset⟩ := origin id allocation
  exact ⟨root,roots id root found,address,offset⟩

theorem RawPointer.Origin.write {pointer : RawPointer} {before after : World}
    {address : Address} {value : Option Value} (origin : pointer.Origin before)
    (written : before.write address value = some after) : pointer.Origin after :=
  origin.transport (World.write_locations written)

theorem RawPointer.Origin.clear {pointer : RawPointer} {before after : World} {addresses : List Address}
    (origin : pointer.Origin before) (cleared : Clears before addresses after) : pointer.Origin after := by
  induction cleared with
  | nil => exact origin
  | cons written _ ih => exact ih (origin.write written)

theorem RawPointer.Origin.retire {pointer : RawPointer} {before after : World} {id : Identity}
    (origin : pointer.Origin before) (retired : Retires before id after) : pointer.Origin after := by
  cases retired with
  | vacant selected _ _ _ =>
      intro target allocation
      obtain ⟨root,found,address,offset⟩ := origin target allocation
      by_cases same : target = id
      · subst target
        have equal := Option.some.inj (selected.symm.trans found)
        subst root
        exact ⟨_,Table.get_set _ _ _,address,offset⟩
      · exact ⟨root,by simpa [Table.get_set_other _ _ _ _ same] using found,address,offset⟩

namespace Memory

theorem AddressOnly.origin (world : World) (integer : Nat) : (AddressOnly integer).Origin world := by
  intro id impossible
  cases impossible

theorem AllocatesBuffer.origin {program : Program} {before after : World}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program before domain element count base pointer after) : pointer.Origin after := by
  cases allocated with
  | fresh =>
      intro id allocation
      have equal := Option.some.inj allocation
      subst id
      exact ⟨_,Table.get_set _ _ _,by simp,by simp⟩

theorem AllocatesBuffer.bound {program : Program} {before after : World}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program before domain element count base pointer after) :
    pointer.address < 2^program.input.target.pointerBits := by
  cases allocated with
  | fresh _ _ _ _ _ _ _ _ extent _ => exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) extent

theorem PointerOffset.origin {program : Program} {world : World} {pointer result : RawPointer} {bytes : Int}
    (offset : PointerOffset program world pointer bytes result) : result.Origin world := by
  obtain ⟨id,root,amount,allocation,found,_,_,_,_,bound,_,rfl⟩ := offset
  intro target selected
  have same := Option.some.inj (allocation.symm.trans selected)
  subst target
  exact ⟨root,found,rfl,bound⟩

theorem WithAddress.origin {program : Program} {world : World} {pointer result : RawPointer} {address : Nat}
    (changed : WithAddress program world pointer address result) : result.Origin world := by
  obtain ⟨id,root,allocation,found,_,_,lower,upper,_,rfl⟩ := changed
  intro target selected
  have same := Option.some.inj (allocation.symm.trans selected)
  subst target
  exact ⟨root,found,by dsimp; omega,by dsimp; omega⟩

theorem PointerOffset.bound {program : Program} {world : World} {pointer result : RawPointer} {bytes : Int}
    (offset : PointerOffset program world pointer bytes result) : result.address < 2^program.input.target.pointerBits := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,bound,rfl⟩ := offset
  exact bound

theorem WithAddress.bound {program : Program} {world : World} {pointer result : RawPointer} {address : Nat}
    (changed : WithAddress program world pointer address result) : result.address < 2^program.input.target.pointerBits := by
  obtain ⟨_,_,_,_,_,_,_,_,bound,rfl⟩ := changed
  exact bound

theorem InstallsResidents.pointer_origin {program : Program} {pointer : RawPointer} {before after : World}
    {addresses : List Address} {values : List (Option Value)}
    (origin : pointer.Origin before) (installed : InstallsResidents program before addresses values after) : pointer.Origin after := by
  induction installed with
  | nil => exact origin
  | hole _ _ ih => exact ih origin
  | resident _ _ written _ ih => exact ih (origin.write written)

theorem BulkMove.pointer_origin {program : Program} {pointer : RawPointer} {before after : World} {sources destinations : List Address}
    (origin : pointer.Origin before) (moved : BulkMove program before sources destinations after) : pointer.Origin after := by
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  exact installed.pointer_origin (origin.clear cleared)

theorem ReleasesBuffer.pointer_origin {pointer released : RawPointer} {program : Program} {before after : World} {domain : Identity}
    (origin : pointer.Origin before) (release : ReleasesBuffer program before released domain after) : pointer.Origin after := by
  cases release with
  | release _ _ _ _ _ _ _ _ _ _ _ _ written retired closed =>
      have coherent := (origin.write written).retire retired
      obtain ⟨_,rfl⟩ := closed
      exact coherent

theorem ReallocatesBuffer.origin {program : Program} {before after : World} {old result : RawPointer}
    {domain : Identity} {element : Term} {count base : Nat}
    (reallocated : ReallocatesBuffer program before old domain element count base result after) : result.Origin after := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,allocated,_,moved,released⟩ := reallocated
  exact released.pointer_origin (moved.pointer_origin allocated.origin)

theorem ReallocatesBuffer.bound {program : Program} {before after : World} {old result : RawPointer}
    {domain : Identity} {element : Term} {count base : Nat}
    (reallocated : ReallocatesBuffer program before old domain element count base result after) :
    result.address < 2^program.input.target.pointerBits := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,allocated,_⟩ := reallocated
  exact allocated.bound

end Memory

theorem RawRange.origin {program : Program} {world : World} {pointer : RawPointer} {length alignment : Nat}
    (range : RawRange program world pointer length alignment) : pointer.Origin world := by
  obtain ⟨id,root,_,allocation,found,_,_,_,_,address,bound,_⟩ := range
  intro target selected
  have same := Option.some.inj (allocation.symm.trans selected)
  subst target
  exact ⟨root,found,address,Nat.le_trans (Nat.le_add_right _ _) bound⟩

namespace Execution

/-- The real primitive output installer establishes the resident and its
typing from the pointer producer, not from a typed post-state. -/
theorem StoresPointer.typed_result {program : Kernel.Program} {before after : World}
    {destination : Address} {mode : Mutability} {type : Term} {pointer : RawPointer}
    (bound : pointer.address < 2^program.declarations.input.target.pointerBits)
    (origin : pointer.Origin before) (stored : StoresPointer program before destination mode type pointer after) :
    ∃ value, after.Stores destination value ∧ Typing.ValueTyped program after value ∧ value.head = .pointer pointer := by
  rcases stored with ⟨_,stored⟩
  cases stored with
  | construct _ _ sources _ _ _ cleared written =>
      cases sources
      cases cleared
      have coherent := origin.write written
      refine ⟨.resident before.nextOwner (.rawPointer mode type) (.pointer pointer) true [],?_,.pointer bound coherent,rfl⟩
      have found := World.write_read_inside written []
      simpa [Value.atPath,World.Stores,World.read,World.root] using found

/-- Every pointer-producing machine primitive reaches a typed installed
pointer. This composes allocation/reallocation/address derivation with the
actual destination write, and uses no resource-admission hypothesis. -/
theorem PrimitiveStep.pointer_result_typed {program : Kernel.Program} {before after : State}
    {event : Option Event} {context : Context} {destination : Address} {binding : RuntimeBinding}
    {arguments : List Term} {operands : List ResolvedPlace} {next : Kernel.Code}
    (step : PrimitiveStep program before event after)
    (task : before.task = .primitive context destination binding arguments operands next)
    (produces : binding.primitive = some .allocate ∨ binding.primitive = some .reallocate ∨
      binding.primitive = some .pointerOffset ∨ binding.primitive = some .pointerWithAddress) :
    ∃ value, after.world.Stores destination value ∧ Typing.ValueTyped program after.world value ∧
      ∃ pointer, value.head = .pointer pointer := by
  cases step <;> simp_all
  case scalar =>
    rename_i calculation _
    cases calculation <;> simp_all
  case scalarFault =>
    rename_i calculation
    cases calculation <;> simp_all
  case allocate =>
    rename_i allocated stored
    obtain ⟨value,found,typed,head⟩ := stored.typed_result allocated.bound allocated.origin
    exact ⟨value,found,typed,_,head⟩
  case reallocate =>
    rename_i allocated stored
    obtain ⟨value,found,typed,head⟩ := stored.typed_result allocated.bound allocated.origin
    exact ⟨value,found,typed,_,head⟩
  case pointerOffset =>
    rename_i offset stored
    obtain ⟨value,found,typed,head⟩ := stored.typed_result offset.bound offset.origin
    exact ⟨value,found,typed,_,head⟩
  case pointerWithAddress =>
    rename_i changed stored
    obtain ⟨value,found,typed,head⟩ := stored.typed_result changed.bound changed.origin
    exact ⟨value,found,typed,_,head⟩

theorem Relocation.pointer_metadata (map : Relocation) (pointer : RawPointer) :
    (map.pointer pointer).offset = pointer.offset ∧
    (map.pointer pointer).generation = pointer.generation ∧
    (map.pointer pointer).domain = pointer.domain := by
  unfold Relocation.pointer
  split
  · exact ⟨rfl,rfl,rfl⟩
  · split
    · split <;> exact ⟨rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl,rfl⟩

/-- The copied pointer selects the copied allocation, with the same extent
and offset. Failure to find physical storage is impossible from the input
provenance and the executable snapshot allocation contract. -/
theorem SnapshotMap.pointer_target {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {pointer : RawPointer} {id : Identity} {homes : Table Home}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (origin : pointer.Origin before.world) (allocation : pointer.allocation = some id) (included : id ∈ map.roots) :
    ∃ root base,
      before.world.roots.get id = some root ∧ map.physical.get id = some base ∧
      (map.copyWorld before.world homes).roots.get (map.root id) =
        some (map.rootValue id { root with home := (homes.get id).getD root.home }) ∧
      map.pointer pointer = { pointer with address := base + pointer.offset, allocation := some (map.root id) } ∧
      pointer.offset ≤ root.layout.size ∧ base + pointer.offset < 2^program.declarations.input.target.pointerBits := by
  obtain ⟨root,found,_,bound⟩ := origin id allocation
  obtain ⟨base,physical,_,_,extent,_⟩ := selected.physical id root included found
  exact ⟨root,base,found,physical,selected.copied_root valid found included,
    by simp [Relocation.pointer,allocation,included,physical],bound,
    Nat.lt_of_le_of_lt (Nat.add_le_add_left bound _) extent⟩

theorem SnapshotMap.pointer_origin {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {pointer : RawPointer} {homes : Table Home}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (origin : pointer.Origin before.world) : (map.pointer pointer).Origin (map.copyWorld before.world homes) := by
  cases allocation : pointer.allocation with
  | none =>
      simpa [Relocation.pointer,allocation] using
        origin.weaken (fun _ _ found => Relocation.old_root found)
  | some id =>
      by_cases included : id ∈ map.roots
      · obtain ⟨root,base,_,physical,found,result,bound,_⟩ :=
          selected.pointer_target (homes := homes) valid origin allocation included
        rw [result]
        intro target present
        have equal : map.root id = target := Option.some.inj present
        subst target
        exact ⟨_,found,by simp [Relocation.rootValue,physical],bound⟩
      · simpa [Relocation.pointer,allocation,included] using
          origin.weaken (fun _ _ found => Relocation.old_root found)

theorem SnapshotMap.pointer_bound {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {pointer : RawPointer}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (origin : pointer.Origin before.world) (bound : pointer.address < 2^program.declarations.input.target.pointerBits) :
    (map.pointer pointer).address < 2^program.declarations.input.target.pointerBits := by
  cases allocation : pointer.allocation with
  | none => simpa [Relocation.pointer,allocation] using bound
  | some id =>
      by_cases included : id ∈ map.roots
      · obtain ⟨_,_,_,_,_,result,_,bound⟩ :=
          selected.pointer_target (homes := suspension.homes) valid origin allocation included
        simpa [result] using bound
      · simpa [Relocation.pointer,allocation,included] using bound

theorem CopiesSnapshot.pointer_typed {program : Kernel.Program} {before after : State} {suspension : Suspension}
    {map : Relocation} {owner : Identity} {mode : Mutability} {type : Term} {pointer : RawPointer} {live : Bool}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (typed : Typing.ValueTyped program before.world (.resident owner (.rawPointer mode type) (.pointer pointer) live [])) :
    Typing.ValueTyped program after.world (map.value (.resident owner (.rawPointer mode type) (.pointer pointer) live [])) := by
  cases typed with
  | aggregate head _ =>
      rcases head with ⟨impossible,_⟩ | ⟨_,_,_,_,impossible,_⟩ | ⟨_,_,_,_,_,impossible,_⟩ <;> cases impossible
  | pointer bound origin =>
      rw [copied.result]
      simp only [Relocation.value,Relocation.term,Term.renameRuntimeRegions,Relocation.values]
      exact .pointer (copied.relocation.pointer_bound valid origin bound)
        (copied.relocation.pointer_origin valid origin)

end Execution
end Glorious.Language
