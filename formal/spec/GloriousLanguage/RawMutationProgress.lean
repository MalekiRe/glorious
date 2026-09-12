import GloriousLanguage.BufferReleaseProgress

/-! Constructive progress for admitted raw moves. Physical provenance and
range facts come from the actual pointer/address relation; ownership and the
whole pending write footprint come from the ordinary transfer contract. -/
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

end Execution
end Glorious.Language
