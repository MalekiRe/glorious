import GloriousLanguage.BufferReleaseProgress
import GloriousLanguage.InputBatchProgress
import GloriousLanguage.CopyProgress
import GloriousLanguage.ScalarStorageProgress
import GloriousLanguage.MemoryPreservation

/-! Constructive progress for admitted raw moves, copies, checked references
and pointer arithmetic. Physical provenance comes from the actual pointer and
resident relations; access, support and new-loan compatibility use the ordinary
value contracts. Numeric bounds never stand in for ownership permission. -/
namespace Glorious.Language

theorem World.Stores.disjoint_empty_root {world : World} {source destination : Address} {value : Value}
    (stored : world.Stores source value) (empty : world.Vacant destination) (whole : destination.fields = []) :
    ¬ source.Overlaps destination := by
  intro overlap
  exact empty.not_stored (stored.prefix
    ⟨overlap.1.symm,overlap.2.1.symm,source.fields,by simp [whole]⟩)

theorem Transfers.read_disjoint {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination address : Address}
    (moved : Transfers program before authority source destination after)
    (sourceApart : ¬ source.Overlaps address) (destinationApart : ¬ destination.Overlaps address) :
    after.read address = before.read address := by
  cases moved with
  | move _ _ _ _ _ _ _ clear install =>
    exact (World.write_disjoint install destinationApart).trans (World.write_disjoint clear sourceApart)

namespace Memory

theorem PointsTo.addressType {program : Program} {world : World} {pointer : RawPointer} {address : Address} {type : Term}
    (points : PointsTo program world pointer address type) : AddressType program world address type := by
  obtain ⟨_,_,_,root,offset,_,located,_⟩ := points
  exact ⟨offset,located⟩

theorem RawMoveRange.length {program : Program} {world : World} {pointer : RawPointer}
    {type : Term} {count : Nat} {places : List ResolvedPlace}
    (range : RawMoveRange program world pointer type count places) : places.length = count := by
  obtain ⟨_,_,_,_,_,slots,_⟩ := range
  simpa [Slots] using congrArg List.length slots

theorem RawMoveRange.pairwise {program : Program} {world : World} {pointer : RawPointer}
    {type : Term} {count : Nat} {places : List ResolvedPlace}
    (range : RawMoveRange program world pointer type count places) :
    places.Pairwise (fun first last => ¬ first.address.Overlaps last.address) := by
  obtain ⟨_,base,start,_,_,slots,_⟩ := range
  have apart : (places.map ResolvedPlace.address).Pairwise (fun first last => ¬ first.Overlaps last) := by
    rw [slots]
    exact Slots.pairwise base start count
  exact List.pairwise_map.mp apart

theorem RawMoveRange.addressType {program : Program} {world : World} {pointer : RawPointer}
    {type : Term} {count : Nat} {places : List ResolvedPlace} {place : ResolvedPlace}
    (range : RawMoveRange program world pointer type count places) (member : place ∈ places) :
    AddressType program world place.address type := by
  obtain ⟨_,_,_,_,_,_,points⟩ := range
  obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
  exact (points index place selected).addressType

theorem RawRead.move_exists {program : Kernel.Program} {before : World}
    {source : ResolvedPlace} {pointer : RawPointer} {type : Term} {layout : Layout}
    {destination : Address} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (points : PointsTo program.declarations before pointer source.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before pointer layout.size layout.alignment)
    (stored : before.Stores source.address value) (initialized : value.Initialized)
    (ready : value.MoveReady program before [source.address,destination])
    (permission : Permitted before source.authority .owned source.address)
    (destinationType : Execution.DestinationType before destination type) :
    ∃ after, RawRead program before source pointer type false destination after ∧ Typing.WorldTyped program after ∧
      after.Stores destination value ∧ Typing.ValueTyped program after value ∧ value.type = type ∧
        value.ResourcesAccessible program after .owned := by
  obtain ⟨offset,located⟩ := points.addressType
  have valueType := located.stored_type valid inventory typed.roots stored
  obtain ⟨after,moved⟩ := Transfers.exists stored initialized ready permission destinationType.vacant
    (stored.disjoint_empty_root destinationType.vacant destinationType.1)
    (valueType.symm ▸ destinationType.addressType)
  have afterTyped := moved.worldTyped valid inventory typed
  obtain ⟨found,_,accessible⟩ := moved.handed_off_ready stored
  exact ⟨after,.read points layoutOf range (Or.inr ⟨rfl,moved⟩),afterTyped,found,
    World.stores_typed afterTyped.roots found,valueType,accessible⟩

theorem RawRead.copy_exists {program : Kernel.Program} {before : World}
    {source : ResolvedPlace} {pointer : RawPointer} {type : Term} {layout : Layout}
    {destination : Address} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (points : PointsTo program.declarations before pointer source.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before pointer layout.size layout.alignment)
    (stored : before.Stores source.address value) (initialized : value.Initialized)
    (ready : value.HandoffReady program before .shared [destination])
    (capability : PrincipalOf program.declarations type .duplicable)
    (permission : Permitted before source.authority .shared source.address)
    (destinationType : Execution.DestinationType before destination type) :
    ∃ after result, RawRead program before source pointer type true destination after ∧
      Typing.WorldTyped program after ∧ after.Stores source.address value ∧
      after.Stores destination result ∧ Typing.ValueTyped program after result ∧ result.type = type ∧
      result.Initialized ∧ result.ResourcesAccessible program after .owned := by
  obtain ⟨offset,located⟩ := points.addressType
  have valueType := located.stored_type valid inventory typed.roots stored
  obtain ⟨after,copied,afterTyped⟩ := Copies.exists valid inventory typed stored initialized ready
    (valueType.symm ▸ capability) permission destinationType.vacant (valueType.symm ▸ destinationType.addressType)
  obtain ⟨result,found,complete,accessible⟩ := copied.handed_off_ready valid typed
  have sourceApart := stored.disjoint_empty_root destinationType.vacant destinationType.1
  have retained : after.Stores source.address value := by
    cases copied with
    | copy _ _ _ _ _ _ _ written =>
      exact (World.write_disjoint written (fun overlap => sourceApart overlap.symm)).trans stored
  obtain ⟨resultOffset,resultLocated⟩ := AddressType.root_transport copied.locations destinationType.1 destinationType.addressType
  exact ⟨after,result,.read points layoutOf range (Or.inl ⟨rfl,copied⟩),afterTyped,retained,found,
    World.stores_typed afterTyped.roots found,
    resultLocated.stored_type valid inventory afterTyped.roots found,complete,accessible⟩

/-- Raw reference construction uses the ordinary checked loan producer. The
pointer authenticates location/range, not the source's ownership or the fresh
loan's compatibility with references reachable from the source. -/
theorem RawBorrow.exists {program : Kernel.Program} {before : World}
    {source : ResolvedPlace} {pointer : RawPointer} {type : Term} {layout : Layout}
    {mode : Mutability} {region : Identity} {destination : Address} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (points : PointsTo program.declarations before pointer source.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before pointer layout.size layout.alignment)
    (stored : before.Stores source.address value) (initialized : value.Initialized)
    (live : region ∈ before.liveRegions)
    (addressable : Addressable program.declarations ⟨[],[],0,default,false,{}⟩ type)
    (ready : value.ResourcesAccessible program before (if mode = .shared then .shared else .unique))
    (permission : Permitted before source.authority (if mode = .shared then .shared else .unique) source.address)
    (outside : value.SupportOutside before destination)
    (compatible : value.ViewsLoanCompatible before (if mode = .shared then .shared else .unique)
      source.address mode (source.authority.guardLoans before))
    (destinationType : Execution.DestinationType before destination (.reference mode (.runtimeRegion region) type)) :
    ∃ after, RawBorrow program before source pointer type mode region destination after ∧
      Typing.WorldTyped program after ∧ after.Stores source.address value ∧
      after.Stores destination (.resident before.nextOwner (.reference mode (.runtimeRegion region) type)
        (.reference before.nextLoan) true []) ∧
      (Value.resident before.nextOwner (.reference mode (.runtimeRegion region) type)
        (.reference before.nextLoan) true []).Initialized ∧
      (Value.resident before.nextOwner (.reference mode (.runtimeRegion region) type)
        (.reference before.nextLoan) true []).ResourcesAccessible program after .owned := by
  obtain ⟨offset,located⟩ := points.addressType
  have valueType := located.stored_type valid inventory typed.roots stored
  obtain ⟨after,formed⟩ := FormsLoan.exists (program := program) (purpose := .source) stored
    (valueType.symm ▸ points.addressType) initialized live (valueType.symm ▸ addressable)
    ready permission destinationType.vacant (valueType.symm ▸ destinationType.addressType)
  have afterTyped := formed.worldTyped valid inventory typed
  have sourceApart := stored.disjoint_empty_root destinationType.vacant destinationType.1
  have separate : ¬ destination.Overlaps source.address := fun overlap => sourceApart overlap.symm
  obtain ⟨actualType,found,complete,accessible⟩ := formed.handed_off_ready typed.1 stored separate outside compatible
  obtain ⟨resultOffset,resultLocated⟩ := AddressType.root_transport formed.locations destinationType.1 destinationType.addressType
  have typeEq := resultLocated.stored_type valid inventory afterTyped.roots found
  have same : actualType = type := (Term.reference.inj typeEq).2.2
  subst actualType
  have retained : after.Stores source.address value := by
    cases formed with
    | borrow _ _ _ _ _ _ _ _ _ _ written => exact (World.write_disjoint written separate).trans stored
  exact ⟨after,.borrow points layoutOf range ⟨value,stored,initialized⟩ formed,
    afterTyped,retained,found,complete,accessible⟩


/-- The extra result slot is part of the same evaluated value's pending
footprint. The actual RawWrite consumes its source/target prefix; its unit
installer consumes the retained protection of the final result slot. -/
theorem RawWrite.exists_with_result {program : Kernel.Program} {before : World}
    {source target : ResolvedPlace} {pointer : RawPointer} {type : Term} {layout : Layout}
    {destination : Address} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (stored : before.Stores source.address value) (valueType : value.type = type) (initialized : value.Initialized)
    (ready : value.MoveReady program before [source.address,target.address,destination])
    (permission : Permitted before source.authority .owned source.address)
    (points : PointsTo program.declarations before pointer target.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before pointer layout.size layout.alignment)
    (writable : Permitted before target.authority .unique target.address)
    (vacant : before.Vacant target.address) (apart : ¬ source.address.Overlaps target.address)
    (resultApart : ¬ target.address.Overlaps destination)
    (destinationType : Execution.DestinationType before destination .unit) :
    ∃ written after, RawWrite program before source target pointer type written ∧
      Execution.StoresUnit program written destination after ∧ Typing.WorldTyped program after ∧
      after.Stores target.address value ∧ Typing.ValueTyped program after value ∧
        value.ResourcesAccessible program after .owned := by
  have transferReady : value.MoveReady program before [source.address,target.address] :=
    ⟨ready.1,fun address member => ready.2 address (List.mem_append_left [destination] member)⟩
  obtain ⟨written,moved⟩ := Transfers.exists stored initialized transferReady permission vacant apart
    (valueType.symm ▸ points.addressType)
  have writtenTyped := moved.worldTyped valid inventory typed
  have sourceApart := stored.disjoint_empty_root destinationType.vacant destinationType.1
  have resultType := destinationType.frame moved.locations (moved.read_disjoint sourceApart resultApart)
  obtain ⟨after,unit⟩ := Execution.StoresUnit.exists (program := program) resultType
  have afterTyped := unit.worldTyped valid inventory writtenTyped
  have framed := ready.frame (.of_locations moved.locations) moved.loans (moved.supportFramed stored)
  have found := (moved.handed_off_ready stored).1
  have finalStored : after.Stores target.address value :=
    (unit.read_disjoint (fun overlap => resultApart overlap.symm)).trans found
  exact ⟨written,after,.write stored valueType points layoutOf range writable moved,unit,afterTyped,finalStored,
    World.stores_typed afterTyped.roots finalStored,
    unit.resourcesAccessible framed.1 (framed.2 destination (by simp))⟩

end Memory

namespace Execution

open Memory

theorem PrimitiveStep.rawRead_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {pointerAddress source : ResolvedPlace} {pointer : RawPointer} {next : Kernel.Code}
    {value : Value} {layout : Layout}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [pointerAddress] next)
    (identity : binding.primitive = some .rawRead) (pointerAt : PointerAt before.world pointerAddress pointer)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) source)
    (points : PointsTo program.declarations before.world pointer source.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before.world pointer layout.size layout.alignment)
    (stored : before.world.Stores source.address value) (initialized : value.Initialized)
    (ready : value.MoveReady program before.world [source.address,destination])
    (permission : Permitted before.world source.authority .owned source.address)
    (destinationType : DestinationType before.world destination type) :
    ∃ after, PrimitiveStep program before none after ∧ Typing.WorldTyped program after.world ∧
      after.world.Stores destination value ∧ Typing.ValueTyped program after.world value ∧ value.type = type ∧
        value.ResourcesAccessible program after.world .owned ∧ after.task = .run context next := by
  obtain ⟨after,read,afterTyped,found,valueTyped,valueType,accessible⟩ := RawRead.move_exists valid inventory typed
    points layoutOf range stored initialized ready permission destinationType
  exact ⟨_,.rawRead task identity pointerAt resource read,afterTyped,found,valueTyped,valueType,accessible,rfl⟩

theorem Step.rawRead_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {pointerAddress source : ResolvedPlace} {pointer : RawPointer} {next : Kernel.Code}
    {value : Value} {layout : Layout}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [pointerAddress] next)
    (identity : binding.primitive = some .rawRead) (pointerAt : PointerAt before.world pointerAddress pointer)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) source)
    (points : PointsTo program.declarations before.world pointer source.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before.world pointer layout.size layout.alignment)
    (stored : before.world.Stores source.address value) (initialized : value.Initialized)
    (ready : value.MoveReady program before.world [source.address,destination])
    (permission : Permitted before.world source.authority .owned source.address)
    (destinationType : DestinationType before.world destination type) :
    ∃ after, Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      after.world.Stores destination value ∧ Typing.ValueTyped program after.world value ∧ value.type = type ∧
        value.ResourcesAccessible program after.world .owned ∧ after.task = .run context next := by
  obtain ⟨after,stepped,afterTyped,result⟩ := PrimitiveStep.rawRead_typed_progress valid inventory typed
    task identity pointerAt resource points layoutOf range stored initialized ready permission destinationType
  exact ⟨after,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl stepped)))),afterTyped,result⟩

theorem PrimitiveStep.rawWrite_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {source pointerAddress target : ResolvedPlace} {pointer : RawPointer} {next : Kernel.Code}
    {value : Value} {layout : Layout}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [source,pointerAddress] next)
    (identity : binding.primitive = some .rawWrite) (pointerAt : PointerAt before.world pointerAddress pointer)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) target)
    (stored : before.world.Stores source.address value) (valueType : value.type = type) (initialized : value.Initialized)
    (ready : value.MoveReady program before.world [source.address,target.address,destination])
    (permission : Permitted before.world source.authority .owned source.address)
    (points : PointsTo program.declarations before.world pointer target.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before.world pointer layout.size layout.alignment)
    (writable : Permitted before.world target.authority .unique target.address)
    (vacant : before.world.Vacant target.address) (apart : ¬ source.address.Overlaps target.address)
    (resultApart : ¬ target.address.Overlaps destination)
    (destinationType : DestinationType before.world destination .unit) :
    ∃ after, PrimitiveStep program before none after ∧ Typing.WorldTyped program after.world ∧
      after.world.Stores target.address value ∧ Typing.ValueTyped program after.world value ∧
      value.ResourcesAccessible program after.world .owned ∧
      ∃ result, after.world.Stores destination result ∧ Typing.ValueTyped program after.world result ∧
        result.type = .unit ∧ result.head = .unit ∧ after.task = .run context next := by
  obtain ⟨written,after,write,unit,afterTyped,found,valueTyped,accessible⟩ := RawWrite.exists_with_result valid inventory typed
    stored valueType initialized ready permission points layoutOf range writable vacant apart resultApart destinationType
  obtain ⟨result,resultFound,resultTyped,resultType,head⟩ := unit.typed_result
  exact ⟨_,.rawWrite task identity pointerAt resource write unit,afterTyped,found,valueTyped,accessible,
    result,resultFound,resultTyped,resultType,head,rfl⟩

theorem Step.rawWrite_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {source pointerAddress target : ResolvedPlace} {pointer : RawPointer} {next : Kernel.Code}
    {value : Value} {layout : Layout}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [source,pointerAddress] next)
    (identity : binding.primitive = some .rawWrite) (pointerAt : PointerAt before.world pointerAddress pointer)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) target)
    (stored : before.world.Stores source.address value) (valueType : value.type = type) (initialized : value.Initialized)
    (ready : value.MoveReady program before.world [source.address,target.address,destination])
    (permission : Permitted before.world source.authority .owned source.address)
    (points : PointsTo program.declarations before.world pointer target.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before.world pointer layout.size layout.alignment)
    (writable : Permitted before.world target.authority .unique target.address)
    (vacant : before.world.Vacant target.address) (apart : ¬ source.address.Overlaps target.address)
    (resultApart : ¬ target.address.Overlaps destination)
    (destinationType : DestinationType before.world destination .unit) :
    ∃ after, Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      after.world.Stores target.address value ∧ Typing.ValueTyped program after.world value ∧
      value.ResourcesAccessible program after.world .owned ∧
      ∃ result, after.world.Stores destination result ∧ Typing.ValueTyped program after.world result ∧
        result.type = .unit ∧ result.head = .unit ∧ after.task = .run context next := by
  obtain ⟨after,stepped,afterTyped,result⟩ := PrimitiveStep.rawWrite_typed_progress valid inventory typed
    task identity pointerAt resource stored valueType initialized ready permission points layoutOf range writable vacant apart
    resultApart destinationType
  exact ⟨after,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl stepped)))),afterTyped,result⟩

theorem PrimitiveStep.rawCopy_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {pointerAddress source : ResolvedPlace} {pointer : RawPointer} {next : Kernel.Code}
    {value : Value} {layout : Layout}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [pointerAddress] next)
    (identity : binding.primitive = some .rawCopy) (pointerAt : PointerAt before.world pointerAddress pointer)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) source)
    (points : PointsTo program.declarations before.world pointer source.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before.world pointer layout.size layout.alignment)
    (stored : before.world.Stores source.address value) (initialized : value.Initialized)
    (ready : value.HandoffReady program before.world .shared [destination])
    (capability : PrincipalOf program.declarations type .duplicable)
    (permission : Permitted before.world source.authority .shared source.address)
    (destinationType : DestinationType before.world destination type) :
    ∃ after result, PrimitiveStep program before none after ∧ Typing.WorldTyped program after.world ∧
      after.world.Stores source.address value ∧ after.world.Stores destination result ∧
      Typing.ValueTyped program after.world result ∧ result.type = type ∧ result.Initialized ∧
      result.ResourcesAccessible program after.world .owned ∧ after.task = .run context next := by
  obtain ⟨after,result,read,afterTyped,retained,found,valueTyped,valueType,complete,accessible⟩ :=
    RawRead.copy_exists valid inventory typed points layoutOf range stored initialized ready capability permission destinationType
  exact ⟨_,result,.rawCopy task identity pointerAt resource read,afterTyped,retained,found,valueTyped,valueType,
    complete,accessible,rfl⟩

theorem Step.rawCopy_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {pointerAddress source : ResolvedPlace} {pointer : RawPointer} {next : Kernel.Code}
    {value : Value} {layout : Layout}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [pointerAddress] next)
    (identity : binding.primitive = some .rawCopy) (pointerAt : PointerAt before.world pointerAddress pointer)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) source)
    (points : PointsTo program.declarations before.world pointer source.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before.world pointer layout.size layout.alignment)
    (stored : before.world.Stores source.address value) (initialized : value.Initialized)
    (ready : value.HandoffReady program before.world .shared [destination])
    (capability : PrincipalOf program.declarations type .duplicable)
    (permission : Permitted before.world source.authority .shared source.address)
    (destinationType : DestinationType before.world destination type) :
    ∃ after result, Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      after.world.Stores source.address value ∧ after.world.Stores destination result ∧
      Typing.ValueTyped program after.world result ∧ result.type = type ∧ result.Initialized ∧
      result.ResourcesAccessible program after.world .owned ∧ after.task = .run context next := by
  obtain ⟨after,result,stepped,afterTyped,rest⟩ := PrimitiveStep.rawCopy_typed_progress valid inventory typed
    task identity pointerAt resource points layoutOf range stored initialized ready capability permission destinationType
  exact ⟨after,result,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl stepped)))),afterTyped,rest⟩

theorem PrimitiveStep.rawBorrow_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {pointerAddress source : ResolvedPlace} {pointer : RawPointer} {next : Kernel.Code}
    {value : Value} {layout : Layout} {mode : Mutability}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [.reference mode (.runtimeRegion context.region) type] [pointerAddress] next)
    (identity : binding.primitive = some .rawBorrow) (pointerAt : PointerAt before.world pointerAddress pointer)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) source)
    (points : PointsTo program.declarations before.world pointer source.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before.world pointer layout.size layout.alignment)
    (stored : before.world.Stores source.address value) (initialized : value.Initialized)
    (live : context.region ∈ before.world.liveRegions)
    (addressable : Addressable program.declarations ⟨[],[],0,default,false,{}⟩ type)
    (ready : value.ResourcesAccessible program before.world (if mode = .shared then .shared else .unique))
    (permission : Permitted before.world source.authority (if mode = .shared then .shared else .unique) source.address)
    (outside : value.SupportOutside before.world destination)
    (compatible : value.ViewsLoanCompatible before.world (if mode = .shared then .shared else .unique)
      source.address mode (source.authority.guardLoans before.world))
    (destinationType : DestinationType before.world destination (.reference mode (.runtimeRegion context.region) type)) :
    ∃ after, PrimitiveStep program before (some (.borrow source.address before.world.nextLoan)) after ∧
      Typing.WorldTyped program after.world ∧ after.world.Stores source.address value ∧
      after.world.Stores destination (.resident before.world.nextOwner (.reference mode (.runtimeRegion context.region) type)
        (.reference before.world.nextLoan) true []) ∧
      (Value.resident before.world.nextOwner (.reference mode (.runtimeRegion context.region) type)
        (.reference before.world.nextLoan) true []).Initialized ∧
      (Value.resident before.world.nextOwner (.reference mode (.runtimeRegion context.region) type)
        (.reference before.world.nextLoan) true []).ResourcesAccessible program after.world .owned ∧
      after.task = .run context next := by
  obtain ⟨after,borrowed,afterTyped,retained,found,complete,accessible⟩ := RawBorrow.exists valid inventory typed
    points layoutOf range stored initialized live addressable ready permission outside compatible destinationType
  exact ⟨_,.rawBorrow task identity pointerAt resource borrowed,afterTyped,retained,found,complete,accessible,rfl⟩

theorem Step.rawBorrow_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {pointerAddress source : ResolvedPlace} {pointer : RawPointer} {next : Kernel.Code}
    {value : Value} {layout : Layout} {mode : Mutability}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [.reference mode (.runtimeRegion context.region) type] [pointerAddress] next)
    (identity : binding.primitive = some .rawBorrow) (pointerAt : PointerAt before.world pointerAddress pointer)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) source)
    (points : PointsTo program.declarations before.world pointer source.address type)
    (layoutOf : LayoutOf program.declarations ⟨[],[],0,default,true,{}⟩ type layout)
    (range : RawRange program.declarations before.world pointer layout.size layout.alignment)
    (stored : before.world.Stores source.address value) (initialized : value.Initialized)
    (live : context.region ∈ before.world.liveRegions)
    (addressable : Addressable program.declarations ⟨[],[],0,default,false,{}⟩ type)
    (ready : value.ResourcesAccessible program before.world (if mode = .shared then .shared else .unique))
    (permission : Permitted before.world source.authority (if mode = .shared then .shared else .unique) source.address)
    (outside : value.SupportOutside before.world destination)
    (compatible : value.ViewsLoanCompatible before.world (if mode = .shared then .shared else .unique)
      source.address mode (source.authority.guardLoans before.world))
    (destinationType : DestinationType before.world destination (.reference mode (.runtimeRegion context.region) type)) :
    ∃ after, Step program host before (some (.borrow source.address before.world.nextLoan)) after ∧
      Typing.WorldTyped program after.world ∧ after.world.Stores source.address value ∧
      after.world.Stores destination (.resident before.world.nextOwner (.reference mode (.runtimeRegion context.region) type)
        (.reference before.world.nextLoan) true []) ∧
      (Value.resident before.world.nextOwner (.reference mode (.runtimeRegion context.region) type)
        (.reference before.world.nextLoan) true []).Initialized ∧
      (Value.resident before.world.nextOwner (.reference mode (.runtimeRegion context.region) type)
        (.reference before.world.nextLoan) true []).ResourcesAccessible program after.world .owned ∧
      after.task = .run context next := by
  obtain ⟨after,stepped,afterTyped,result⟩ := PrimitiveStep.rawBorrow_typed_progress valid inventory typed
    task identity pointerAt resource points layoutOf range stored initialized live addressable ready permission outside compatible destinationType
  exact ⟨after,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl stepped)))),afterTyped,result⟩


theorem PrimitiveStep.pointerOffset_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {pointerAddress offsetAddress : ResolvedPlace} {pointer : RawPointer} {offset : Int}
    {next : Kernel.Code} {mode : Mutability} {id : Identity} {root : Root}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [pointerAddress,offsetAddress] next)
    (identity : binding.primitive = some .pointerOffset) (pointerAt : PointerAt before.world pointerAddress pointer)
    (offsetAt : ScalarAt before.world offsetAddress (.integer true .pointer offset))
    (allocation : pointer.allocation = some id) (found : before.world.roots.get id = some root)
    (live : root.live = true) (generation : root.generation = pointer.generation)
    (lower : 0 ≤ Int.ofNat pointer.offset+offset)
    (upper : (Int.ofNat pointer.offset+offset).toNat ≤ root.layout.size)
    (bound : root.base+(Int.ofNat pointer.offset+offset).toNat < 2^program.declarations.input.target.pointerBits)
    (destinationType : DestinationType before.world destination (.rawPointer mode type)) :
    ∃ after result value, PrimitiveStep program before none after ∧ Typing.WorldTyped program after.world ∧
      PointerOffset program.declarations before.world pointer offset result ∧
      after.world.Stores destination value ∧ Typing.ValueTyped program after.world value ∧
      value.head = .pointer result ∧ after.task = .run context next := by
  let amount := (Int.ofNat pointer.offset+offset).toNat
  let result := { pointer with address := root.base+amount, offset := amount }
  have calculated : PointerOffset program.declarations before.world pointer offset result :=
    ⟨id,root,_,allocation,found,live,generation,lower,rfl,upper,bound,rfl⟩
  obtain ⟨after,stored⟩ := StoresPointer.exists (program := program) result destinationType
  obtain ⟨value,resultFound,valueTyped,head⟩ := stored.typed_result calculated.bound calculated.origin
  exact ⟨_,result,value,.pointerOffset task identity pointerAt offsetAt calculated stored,
    stored.worldTyped valid inventory typed calculated.bound calculated.origin,calculated,resultFound,valueTyped,head,rfl⟩

theorem Step.pointerOffset_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {pointerAddress offsetAddress : ResolvedPlace} {pointer : RawPointer} {offset : Int}
    {next : Kernel.Code} {mode : Mutability} {id : Identity} {root : Root}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [pointerAddress,offsetAddress] next)
    (identity : binding.primitive = some .pointerOffset) (pointerAt : PointerAt before.world pointerAddress pointer)
    (offsetAt : ScalarAt before.world offsetAddress (.integer true .pointer offset))
    (allocation : pointer.allocation = some id) (found : before.world.roots.get id = some root)
    (live : root.live = true) (generation : root.generation = pointer.generation)
    (lower : 0 ≤ Int.ofNat pointer.offset+offset)
    (upper : (Int.ofNat pointer.offset+offset).toNat ≤ root.layout.size)
    (bound : root.base+(Int.ofNat pointer.offset+offset).toNat < 2^program.declarations.input.target.pointerBits)
    (destinationType : DestinationType before.world destination (.rawPointer mode type)) :
    ∃ after result value, Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      PointerOffset program.declarations before.world pointer offset result ∧
      after.world.Stores destination value ∧ Typing.ValueTyped program after.world value ∧
      value.head = .pointer result ∧ after.task = .run context next := by
  obtain ⟨after,result,value,stepped,afterTyped,rest⟩ := PrimitiveStep.pointerOffset_typed_progress valid inventory typed
    task identity pointerAt offsetAt allocation found live generation lower upper bound destinationType
  exact ⟨after,result,value,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl stepped)))),afterTyped,rest⟩

/-- Address replacement retains provenance and generation. Its machine-size
bound follows from the actual unsigned operand, not an after-pointer premise. -/
theorem PrimitiveStep.pointerWithAddress_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {pointerAddress integerAddress : ResolvedPlace} {pointer : RawPointer} {integer : Int}
    {next : Kernel.Code} {mode : Mutability} {id : Identity} {root : Root}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [pointerAddress,integerAddress] next)
    (identity : binding.primitive = some .pointerWithAddress) (pointerAt : PointerAt before.world pointerAddress pointer)
    (integerAt : ScalarAt before.world integerAddress (.integer false .pointer integer))
    (allocation : pointer.allocation = some id) (found : before.world.roots.get id = some root)
    (live : root.live = true) (generation : root.generation = pointer.generation)
    (lower : root.base ≤ integer.toNat) (upper : integer.toNat ≤ root.base+root.layout.size)
    (destinationType : DestinationType before.world destination (.rawPointer mode type)) :
    ∃ after result value, PrimitiveStep program before none after ∧ Typing.WorldTyped program after.world ∧
      WithAddress program.declarations before.world pointer integer.toNat result ∧
      after.world.Stores destination value ∧ Typing.ValueTyped program after.world value ∧
      value.head = .pointer result ∧ after.task = .run context next := by
  have integerBounds := (integerAt.valid typed).2
  change 0 ≤ integer ∧ integer < (2 : Int)^program.declarations.input.target.pointerBits at integerBounds
  have bound : integer.toNat < 2^program.declarations.input.target.pointerBits := by
    have castBound : (integer.toNat : Int) < (2 : Int)^program.declarations.input.target.pointerBits := by omega
    exact_mod_cast castBound
  let result := { pointer with address := integer.toNat, offset := integer.toNat-root.base }
  have calculated : WithAddress program.declarations before.world pointer integer.toNat result :=
    ⟨id,root,allocation,found,live,generation,lower,upper,bound,rfl⟩
  obtain ⟨after,stored⟩ := StoresPointer.exists (program := program) result destinationType
  obtain ⟨value,resultFound,valueTyped,head⟩ := stored.typed_result calculated.bound calculated.origin
  exact ⟨_,result,value,.pointerWithAddress task identity pointerAt integerAt integerBounds.1 calculated stored,
    stored.worldTyped valid inventory typed calculated.bound calculated.origin,calculated,resultFound,valueTyped,head,rfl⟩

theorem Step.pointerWithAddress_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {pointerAddress integerAddress : ResolvedPlace} {pointer : RawPointer} {integer : Int}
    {next : Kernel.Code} {mode : Mutability} {id : Identity} {root : Root}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [pointerAddress,integerAddress] next)
    (identity : binding.primitive = some .pointerWithAddress) (pointerAt : PointerAt before.world pointerAddress pointer)
    (integerAt : ScalarAt before.world integerAddress (.integer false .pointer integer))
    (allocation : pointer.allocation = some id) (found : before.world.roots.get id = some root)
    (live : root.live = true) (generation : root.generation = pointer.generation)
    (lower : root.base ≤ integer.toNat) (upper : integer.toNat ≤ root.base+root.layout.size)
    (destinationType : DestinationType before.world destination (.rawPointer mode type)) :
    ∃ after result value, Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      WithAddress program.declarations before.world pointer integer.toNat result ∧
      after.world.Stores destination value ∧ Typing.ValueTyped program after.world value ∧
      value.head = .pointer result ∧ after.task = .run context next := by
  obtain ⟨after,result,value,stepped,afterTyped,rest⟩ := PrimitiveStep.pointerWithAddress_typed_progress valid inventory typed
    task identity pointerAt integerAt allocation found live generation lower upper destinationType
  exact ⟨after,result,value,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl stepped)))),afterTyped,rest⟩

theorem PrimitiveStep.pointerAddress_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {pointerAddress : ResolvedPlace} {pointer : RawPointer} {next : Kernel.Code}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [] [pointerAddress] next)
    (identity : binding.primitive = some .pointerAddress) (pointerAt : PointerAt before.world pointerAddress pointer)
    (destinationType : DestinationType before.world destination (.scalar (.integer false .pointer))) :
    ∃ after value, PrimitiveStep program before none after ∧ Typing.WorldTyped program after.world ∧
      after.world.Stores destination value ∧ Typing.ValueTyped program after.world value ∧
      value.type = .scalar (.integer false .pointer) ∧ value.head = .scalar (.integer false .pointer pointer.address) ∧
      after.task = .run context next := by
  have bound := (pointerAt.bound_origin typed).1
  have scalarValid : (ScalarValue.integer false .pointer pointer.address).Valid program.declarations.input.target := by
    refine ⟨valid.1.1.2.2.2.2.1.1,?_⟩
    change (0 : Int) ≤ pointer.address ∧ (pointer.address : Int) < (2 : Int)^program.declarations.input.target.pointerBits
    exact ⟨Int.natCast_nonneg _,by exact_mod_cast bound⟩
  obtain ⟨after,stored⟩ := StoresScalar.exists (program := program) scalarValid destinationType
  obtain ⟨value,found,valueTyped,valueType,head⟩ := stored.typed_result
  exact ⟨_,value,.pointerAddress task identity pointerAt stored,stored.worldTyped valid inventory typed,
    found,valueTyped,valueType,head,rfl⟩

theorem Step.pointerAddress_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {pointerAddress : ResolvedPlace} {pointer : RawPointer} {next : Kernel.Code}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [] [pointerAddress] next)
    (identity : binding.primitive = some .pointerAddress) (pointerAt : PointerAt before.world pointerAddress pointer)
    (destinationType : DestinationType before.world destination (.scalar (.integer false .pointer))) :
    ∃ after value, Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      after.world.Stores destination value ∧ Typing.ValueTyped program after.world value ∧
      value.type = .scalar (.integer false .pointer) ∧ value.head = .scalar (.integer false .pointer pointer.address) ∧
      after.task = .run context next := by
  obtain ⟨after,value,stepped,afterTyped,rest⟩ := PrimitiveStep.pointerAddress_typed_progress valid inventory typed
    task identity pointerAt destinationType
  exact ⟨after,value,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl stepped)))),afterTyped,rest⟩


/-- Authenticated pre-state ranges construct the snapshot move and actual
unit result. Neither a moved world nor a result-write witness is admission. -/
theorem PrimitiveStep.rawMove_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {sourcePointerAddress targetPointerAddress countAddress : ResolvedPlace}
    {sourcePointer targetPointer : RawPointer} {count : Int} {next : Kernel.Code}
    {sources destinations : List ResolvedPlace}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [sourcePointerAddress,targetPointerAddress,countAddress] next)
    (identity : binding.primitive = some .rawMove)
    (sourcePointerAt : PointerAt before.world sourcePointerAddress sourcePointer)
    (targetPointerAt : PointerAt before.world targetPointerAddress targetPointer)
    (countAt : ScalarAt before.world countAddress (.integer false .pointer count)) (nonnegative : 0 ≤ count)
    (sourceRange : RawMoveRange program.declarations before.world sourcePointer type count.toNat sources)
    (targetRange : RawMoveRange program.declarations before.world targetPointer type count.toNat destinations)
    (resources : ∀ place ∈ sources ++ destinations,
      Kernel.ResolvesResource before.world context.environment (.activation context.activation) place)
    (located : ∀ source ∈ sources, before.world.Located source.address)
    (permissions : ∀ source ∈ sources, Permitted before.world source.authority .owned source.address ∧
      ∀ value, before.world.Stores source.address value →
        value.MoveReady program before.world (((sources ++ destinations).map ResolvedPlace.address) ++ [destination]))
    (writable : ∀ target ∈ destinations, Permitted before.world target.authority .unique target.address ∧
      (target.address ∈ sources.map ResolvedPlace.address ∨ before.world.Vacant target.address))
    (paths : ∀ source ∈ sources, ∀ target ∈ destinations, ¬ source.address.ProperPrefix target.address)
    (resultApart : ∀ place ∈ sources ++ destinations, ¬ place.address.Overlaps destination)
    (destinationType : DestinationType before.world destination .unit) :
    ∃ after, PrimitiveStep program before none after ∧ Typing.WorldTyped program after.world ∧
      after.task = .run context next ∧
      (∃ result, after.world.Stores destination result ∧ Typing.ValueTyped program after.world result ∧
        result.type = .unit ∧ result.head = .unit) ∧
      (∀ (index : Nat) (source target : ResolvedPlace), sources[index]? = some source → destinations[index]? = some target →
        after.world.read target.address = before.world.read source.address) ∧
      (∀ (source : ResolvedPlace) (value : Value), source ∈ sources → before.world.Stores source.address value →
        value.ResourcesAccessible program after.world .owned) := by
  let values := sources.map (fun source => before.world.read source.address)
  have snapshot : ListRel (fun source value => before.world.read source.address = value) sources values := by
    simpa using (ListRel.maps (relation := fun source value => before.world.read source.address = value)
      sources id (fun source => before.world.read source.address) (fun _ _ => rfl))
  have prepared : ListRel (fun target resident =>
      (target.address ∈ sources.map ResolvedPlace.address ∨ before.world.Vacant target.address) ∧
      ∀ value, resident = some value → AddressType program.declarations before.world target.address value.type)
      destinations values := by
    apply ListRel.of_at (targetRange.length.trans (sourceRange.length.symm.trans snapshot.length_eq))
    intro index target resident targetAt residentAt
    obtain ⟨source,sourceAt,read⟩ := snapshot.get_right residentAt
    refine ⟨(writable target (List.mem_of_getElem? targetAt)).2,?_⟩
    intro value same
    have stored := read.trans same
    obtain ⟨offset,sourceType⟩ := sourceRange.addressType (List.mem_of_getElem? sourceAt)
    have valueType := sourceType.stored_type valid inventory typed.roots stored
    rw [valueType]
    exact targetRange.addressType (List.mem_of_getElem? targetAt)
  have admitted : ∀ source ∈ sources, Permitted before.world source.authority .owned source.address ∧
      ∀ value, before.world.Stores source.address value →
        value.MoveReady program before.world ((sources ++ destinations).map ResolvedPlace.address) := by
    intro source member
    refine ⟨(permissions source member).1,?_⟩
    intro value stored
    have ready := (permissions source member).2 value stored
    exact ⟨ready.1,fun address present => ready.2 address (List.mem_append_left _ present)⟩
  obtain ⟨moved,move⟩ := BulkMove.exists sourceRange.pairwise targetRange.pairwise paths snapshot located admitted
    (fun target member => (writable target member).1) prepared
  have movedTyped := move.worldTyped valid inventory typed
  have resultType := destinationType.frame move.locations (move.read_disjoint resultApart)
  obtain ⟨after,unit⟩ := StoresUnit.exists (program := program) resultType
  refine ⟨{ before with world := after, task := .run context next },
    .rawMove task identity sourcePointerAt targetPointerAt countAt nonnegative sourceRange targetRange resources move unit,
    unit.worldTyped valid inventory movedTyped,rfl,unit.typed_result,?_,?_⟩
  · intro index source target sourceAt targetAt
    have outside : ¬ destination.Overlaps target.address := fun overlap =>
      resultApart target (List.mem_append_right _ (List.mem_of_getElem? targetAt)) overlap.symm
    exact (unit.read_disjoint outside).trans (move.snapshot index source target sourceAt targetAt)
  · intro source value member stored
    have ready := (permissions source member).2 value stored
    have frame : value.SupportFramed before.world moved := by
      intro address supported
      exact ⟨move.read_disjoint (fun place present => ready.2 place.address
        (List.mem_append_left _ (List.mem_map.mpr ⟨place,present,rfl⟩)) address supported),move.locations address.root⟩
    have loans : moved.loans = before.world.loans := by
      simpa using congrArg World.loans move.rest
    have accessible := ready.1.frame (.of_locations move.locations) loans frame
    apply unit.resourcesAccessible accessible
    intro address supported
    exact ready.2 destination (List.mem_append_right _ (by simp)) address
      ((Value.Support.frame loans frame).mpr supported)

theorem Step.rawMove_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term}
    {sourcePointerAddress targetPointerAddress countAddress : ResolvedPlace}
    {sourcePointer targetPointer : RawPointer} {count : Int} {next : Kernel.Code}
    {sources destinations : List ResolvedPlace}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [type] [sourcePointerAddress,targetPointerAddress,countAddress] next)
    (identity : binding.primitive = some .rawMove)
    (sourcePointerAt : PointerAt before.world sourcePointerAddress sourcePointer)
    (targetPointerAt : PointerAt before.world targetPointerAddress targetPointer)
    (countAt : ScalarAt before.world countAddress (.integer false .pointer count)) (nonnegative : 0 ≤ count)
    (sourceRange : RawMoveRange program.declarations before.world sourcePointer type count.toNat sources)
    (targetRange : RawMoveRange program.declarations before.world targetPointer type count.toNat destinations)
    (resources : ∀ place ∈ sources ++ destinations,
      Kernel.ResolvesResource before.world context.environment (.activation context.activation) place)
    (located : ∀ source ∈ sources, before.world.Located source.address)
    (permissions : ∀ source ∈ sources, Permitted before.world source.authority .owned source.address ∧
      ∀ value, before.world.Stores source.address value →
        value.MoveReady program before.world (((sources ++ destinations).map ResolvedPlace.address) ++ [destination]))
    (writable : ∀ target ∈ destinations, Permitted before.world target.authority .unique target.address ∧
      (target.address ∈ sources.map ResolvedPlace.address ∨ before.world.Vacant target.address))
    (paths : ∀ source ∈ sources, ∀ target ∈ destinations, ¬ source.address.ProperPrefix target.address)
    (resultApart : ∀ place ∈ sources ++ destinations, ¬ place.address.Overlaps destination)
    (destinationType : DestinationType before.world destination .unit) :
    ∃ after, Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      after.task = .run context next ∧
      (∃ result, after.world.Stores destination result ∧ Typing.ValueTyped program after.world result ∧
        result.type = .unit ∧ result.head = .unit) ∧
      (∀ (index : Nat) (source target : ResolvedPlace), sources[index]? = some source → destinations[index]? = some target →
        after.world.read target.address = before.world.read source.address) ∧
      (∀ (source : ResolvedPlace) (value : Value), source ∈ sources → before.world.Stores source.address value →
        value.ResourcesAccessible program after.world .owned) := by
  obtain ⟨after,stepped,rest⟩ := PrimitiveStep.rawMove_typed_progress valid inventory typed task identity
    sourcePointerAt targetPointerAt countAt nonnegative sourceRange targetRange resources located permissions writable
    paths resultApart destinationType
  exact ⟨after,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl stepped)))),rest⟩

end Execution
end Glorious.Language
