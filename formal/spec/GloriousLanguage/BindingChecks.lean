import GloriousLanguage.Contracts

namespace Glorious.Language.BindingChecks

open Kernel Execution

private def metadata : BindingPack := ⟨3,2,[7],[⟨10,50,true⟩]⟩
private def packType : Term := .bindings (.runtimeBrand (.proof 3)) (.runtimeRegion 2) [.unit]
private def fieldValue : Value := .resident 12 .unit .unit true []
private def packValue : Value := .resident 11 packType (.bindings metadata) true [some fieldValue]
private def resultValue : Value := .resident 10 (.tuple [packType]) .tuple true [some packValue]
private def source : Address := ⟨0,0,[]⟩
private def destination : Address := ⟨1,0,[]⟩
private def root : Root :=
  ⟨.localSlot 0 2,0,2,1,⟨0,1,[0],0,0,[]⟩,resultValue.type,some resultValue,false,0,true,[]⟩
private def vacant : Root := { root with value := none }
private def world : World :=
  { roots := [(0,root),(1,vacant)], liveRegions := [2], nextRoot := 2,
    nextOwner := 20, nextRegion := 3, nextProof := 4 }
private def cleared : World := { world with roots := world.roots.set 0 vacant }
private def moved : World := { cleared with roots := cleared.roots.set 1 root }

private theorem fieldInitialized : fieldValue.Initialized := by
  intro path resident location
  cases location with
  | root => simp [fieldValue, Value.shellLive, Value.fields]
  | field member _ => simp [fieldValue, Value.fields] at member

private theorem packInitialized : packValue.Initialized := by
  intro path resident location
  cases location with
  | root => simp [packValue, Value.shellLive, Value.fields]
  | @field _ index child path _ member nested =>
      cases index with
      | zero => simp [packValue, Value.fields] at member; subst child; exact fieldInitialized _ _ nested
      | succ index => simp [packValue, Value.fields] at member

private theorem resultInitialized : resultValue.Initialized := by
  intro path resident location
  cases location with
  | root => simp [resultValue, Value.shellLive, Value.fields]
  | @field _ index child path _ member nested =>
      cases index with
      | zero => simp [resultValue, Value.fields] at member; subst child; exact packInitialized _ _ nested
      | succ index => simp [resultValue, Value.fields] at member

private theorem readable (access : Access) : Permitted world .owner access source := by
  refine ⟨⟨root,rfl⟩,?_⟩
  intro id loan found
  simp [world, Table.get] at found

private theorem transferResult (program : Language.Program) : Transfers program world .owner source destination moved := by
  refine .move (value := resultValue) (cleared := cleared) rfl resultInitialized (readable .owned)
    ⟨vacant,rfl,Or.inl ⟨rfl,rfl⟩⟩ ?_ ⟨0,.root (root := vacant) (id := 1) rfl rfl⟩ rfl rfl
  simp [source, destination, Address.Overlaps]

/-- The pack's field is at the new carrier's child path. No address metadata
needs rewriting, and the old field address no longer reads a resident. -/
example (program : Language.Program) : Transfers program world .owner source destination moved ∧
    moved.Stores ((destination.child 0).child 0) fieldValue ∧
    moved.read ((source.child 0).child 0) = none := ⟨transferResult program,rfl,rfl⟩

example : Contracts.Guard.Holds moved (.pattern 10 50 true) := by
  refine ⟨destination.child 0,packValue,metadata,?_,rfl,rfl,by simp [metadata]⟩
  exact ⟨root,resultValue,rfl,rfl,rfl,rfl,.field rfl .root⟩

example : ¬ Contracts.Guard.Holds ({ world with roots := [] }) (.pattern 10 50 true) := by
  rintro ⟨address,value,pack,resident,_,_,_⟩
  rcases resident with ⟨root,whole,found,_,_,_,_⟩
  simp [Table.get] at found

private def copiedMetadata : BindingPack := { metadata with facts := [⟨20,50,true⟩] }
private def copiedField : Value := .resident 22 .unit .unit true []
private def copiedPack : Value := .resident 21 packType (.bindings copiedMetadata) true [some copiedField]
private def copiedResult : Value := .resident 20 resultValue.type .tuple true [some copiedPack]
private def copiedWorld : World :=
  { world with roots := world.roots.set 1 { vacant with value := some copiedResult }, nextOwner := 23 }

private theorem capabilities {program : Language.Program} (model : CapabilityModel program) :
    PrincipalOf program .unit .duplicable ∧ PrincipalOf program packType .duplicable ∧
    PrincipalOf program resultValue.type .duplicable := by
  have unit := (model.equations .unit .duplicable).mpr .unit
  have pack := (model.equations packType .duplicable).mpr (.bindings (.cons unit .nil))
  exact ⟨⟨model,unit⟩,⟨model,pack⟩,⟨model,(model.equations _ _).mpr (.tuple (.cons pack .nil))⟩⟩

private theorem copyResult {program : Language.Program} (model : CapabilityModel program) :
    CopyValue program 20 resultValue 23 copiedResult := by
  obtain ⟨unit,pack,result⟩ := capabilities model
  have tree : CopyTree program 20 resultValue 23
      (.resident 20 resultValue.type .tuple true
        [some (.resident 21 packType (.bindings metadata) true [some copiedField])])
      [(10,20),(11,21),(12,22)] :=
    .resident result (.cons (.resident pack (.cons (.resident unit .nil) .nil)) .nil)
  simpa [copiedResult, copiedPack, copiedMetadata, copiedField, metadata, Value.mapBindingOrigins,
    Value.mapFieldOrigins, BindingPack.mapOrigins, Table.get] using CopyValue.copy tree (by simp [Table.Unique])

/-- Copying the complete result changes both its owner and the nested pack's
reference to that owner. The brand and resident type stay exactly the same. -/
example {program : Language.Program} (model : CapabilityModel program) :
    Copies program world .owner source destination copiedWorld := by
  exact .copy (before := world) (source := source) (destination := destination)
    (value := resultValue) (cloned := copiedResult) rfl resultInitialized (readable .shared)
    ⟨vacant,rfl,Or.inl ⟨rfl,rfl⟩⟩ ⟨0,.root (root := vacant) (id := 1) rfl rfl⟩ (copyResult model) rfl

example : Contracts.Guard.Holds copiedWorld (.pattern 20 50 true) := by
  refine ⟨destination.child 0,copiedPack,copiedMetadata,?_,rfl,rfl,by simp [copiedMetadata]⟩
  exact ⟨{ vacant with value := some copiedResult },copiedResult,rfl,rfl,rfl,rfl,.field rfl .root⟩

example (program : Kernel.Program) : Typing.ValueTyped program copiedWorld copiedPack := by
  exact .bindings (.resident .unit rfl .nil) rfl rfl rfl (by decide)

/-- A separately copied pack still describes the originating result outside
that copied subtree; it does not invent a new result guard for its own owner. -/
example {program : Language.Program} (model : CapabilityModel program) :
    CopyValue program 30 packValue 32
      (.resident 30 packType (.bindings metadata) true [some (.resident 31 .unit .unit true [])]) := by
  obtain ⟨unit,pack,_⟩ := capabilities model
  have tree : CopyTree program 30 packValue 32
      (.resident 30 packType (.bindings metadata) true [some (.resident 31 .unit .unit true [])])
      [(11,30),(12,31)] := .resident pack (.cons (.resident unit .nil) .nil)
  simpa [metadata, Value.mapBindingOrigins, Value.mapFieldOrigins, BindingPack.mapOrigins, Table.get]
    using CopyValue.copy tree (by simp [Table.Unique])

example (map : Relocation) : (map.value packValue).head =
    .bindings ⟨3,map.region 2,[7],[⟨map.owner 10,50,true⟩]⟩ := by
  simp [Relocation.value, packValue, metadata, BindingPack.mapOrigins, Value.head]

example (map : Relocation) (outside : 10 ∉ map.owners) :
    map.owner 10 = 10 := by simp [Relocation.owner, relocateId, outside]

example (program : Kernel.Program) (world : World) (map : Relocation) :
    Typing.ValueTyped program world (map.value packValue) := by
  simp only [packValue, fieldValue, packType, Relocation.value, Relocation.values, Relocation.term, Term.renameRuntimeRegions,
    List.map_cons, List.map_nil]
  change Typing.ValueTyped program world
    (.resident (map.ownerBase+11) (.bindings (.runtimeBrand (.proof 3)) (.runtimeRegion (map.region 2)) [.unit])
      (.bindings { metadata.mapOrigins map.owner with region := map.region 2 }) true
      [some (.resident (map.ownerBase+12) .unit .unit true [])])
  exact .bindings (.resident .unit rfl .nil) rfl rfl rfl (by simp [metadata, BindingPack.mapOrigins])

example {program : Language.Program} {next value finish copied}
    (copy : CopyValue program next value finish copied) : copied.type = value.type := copy.type_eq

end Glorious.Language.BindingChecks
