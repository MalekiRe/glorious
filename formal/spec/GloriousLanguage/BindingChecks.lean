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

/-- The nested result genuinely has no resource and no reference handle, so
its actual reachable graph is already handoff-ready. The argument is
generalized over the access and the pending write footprint because the same
derived fact is consumed by both the move and the copy boundary. -/
private theorem resultHandoffReady (program : RuntimeProgram) (readAccess : Access) (pending : List Address) :
    resultValue.HandoffReady program world readAccess pending := by
  let Plain (value : Value) : Prop := value.resources = [] ∧ value.InvariantClosed program world ∧
    ∀ id, value.head ≠ .reference id
  have fieldPlain : ∀ path value, ResidentAt fieldValue path value → Plain value := by
    intro path value location
    cases location with
    | root => simp [Plain,fieldValue,Value.resources,Value.InvariantClosed,Value.type,Value.head]
    | field member _ => simp [fieldValue,Value.fields] at member
  have packPlain : ∀ path value, ResidentAt packValue path value → Plain value := by
    intro path value location
    cases location with
    | root => simp [Plain,packValue,packType,Value.resources,Value.InvariantClosed,Value.type,Value.head]
    | @field _ index child path _ member nested =>
      cases index with
      | zero => simp [packValue,Value.fields] at member; subst child; exact fieldPlain _ _ nested
      | succ index => simp [packValue,Value.fields] at member
  have resultPlain : ∀ path value, ResidentAt resultValue path value → Plain value := by
    intro path value location
    cases location with
    | root => simp [Plain,resultValue,Value.resources,Value.InvariantClosed,Value.type,Value.head]
    | @field _ index child path _ member nested =>
      cases index with
      | zero => simp [resultValue,Value.fields] at member; subst child; exact packPlain _ _ nested
      | succ index => simp [resultValue,Value.fields] at member
  have reachedPlain : ∀ {authority incoming value current access},
      resultValue.ReachableResident world authority incoming value current access → Plain value := by
    intro authority incoming value current access reached
    induction reached with
    | resident located => exact resultPlain _ _ located
    | referent _ head _ _ _ ih => exact False.elim (ih.2.2 _ head)
    | resource _ member _ _ ih => simp [ih.1] at member
  have noReference : ∀ {authority incoming id current access},
      ¬ resultValue.ReachableReference world authority incoming id current access := by
    rintro authority incoming id current access ⟨value,reached,head⟩
    exact (reachedPlain reached).2.2 id head
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro value authority access reached
    exact ⟨by simp [(reachedPlain reached).1],(reachedPlain reached).2.1⟩
  · intro id authority access reached
    exact False.elim (noReference reached)
  · intro id authority access reached
    exact False.elim (noReference reached)
  · intro value authority access reached binding member
    simp [(reachedPlain reached).1] at member
  · intro mutation _ address support
    rcases support with ⟨value,authority,access,reached,reference | resource⟩
    · obtain ⟨id,loan,head,_⟩ := reference
      exact False.elim ((reachedPlain reached).2.2 id head)
    · obtain ⟨binding,member,_⟩ := resource
      simp [(reachedPlain reached).1] at member

private theorem transferResult (program : RuntimeProgram) : Transfers program world .owner source destination moved := by
  have ready : resultValue.MoveReady program world [source,destination] :=
    resultHandoffReady program .owned [source,destination]
  refine .move (value := resultValue) (cleared := cleared) rfl resultInitialized ready (readable .owned)
    ⟨vacant,rfl,Or.inl ⟨rfl,rfl⟩⟩ ?_ ⟨0,.root (root := vacant) (id := 1) rfl rfl⟩ rfl rfl
  simp [source, destination, Address.Overlaps]

/-- The pack's field is at the new carrier's child path. No address metadata
needs rewriting, and the old field address no longer reads a resident. -/
example (program : RuntimeProgram) : Transfers program world .owner source destination moved ∧
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

/-- The actual composite value types are certified by the canonical
producers: the unit leaf, then the one-field binding set and the one-field
tuple that inherit its duplicable class through finite equation composition.
No capability model is assumed, and the derived principals are the greatest
certified classes rather than a requested bound. -/
private theorem capabilities (program : Language.Program) :
    PrincipalOf program .unit .duplicable ∧ PrincipalOf program packType .duplicable ∧
    PrincipalOf program resultValue.type .duplicable := by
  classical
  have unitEvidence : CapabilityEvidence program { module := default } .unit .duplicable :=
    CapabilityEquation.unit.closedEvidence (program := program) (context := { module := default })
  have packEvidence : CapabilityEvidence program { module := default } packType .duplicable := by
    let assignment : Term → Option Principal := fun term => if term = .unit then some .duplicable else none
    have equation : CapabilityEquation program assignment packType .duplicable :=
      .bindings (fields := [.unit]) (principals := [.duplicable]) (.cons (by simp [assignment]) .nil)
    exact equation.realize (fun term claimed found => by
      by_cases unit : term = .unit
      · rw [unit] at found
        have pair : some .duplicable = some claimed := by simpa [assignment] using found
        have same : claimed = .duplicable := (Option.some.inj pair).symm
        rw [unit, same]
        exact unitEvidence
      · simp [assignment, unit] at found)
  have resultEvidence : CapabilityEvidence program { module := default } resultValue.type .duplicable := by
    let assignment : Term → Option Principal := fun term => if term = packType then some .duplicable else none
    have equation : CapabilityEquation program assignment resultValue.type .duplicable :=
      .tuple (fields := [packType]) (principals := [.duplicable]) (.cons (by simp [assignment]) .nil)
    exact equation.realize (fun term claimed found => by
      by_cases pack : term = packType
      · rw [pack] at found
        have pair : some .duplicable = some claimed := by simpa [assignment] using found
        have same : claimed = .duplicable := (Option.some.inj pair).symm
        rw [pack, same]
        exact packEvidence
      · simp [assignment, pack] at found)
  exact ⟨PrincipalOf.unit program,(packEvidence.support rfl).duplicable,(resultEvidence.support rfl).duplicable⟩

private theorem copyResult {program : Language.Program} :
    CopyValue program 20 resultValue 23 copiedResult := by
  obtain ⟨unit,pack,result⟩ := capabilities program
  have tree : CopyTree program 20 resultValue 23
      (.resident 20 resultValue.type .tuple true
        [some (.resident 21 packType (.bindings metadata) true [some copiedField])])
      [(10,20),(11,21),(12,22)] :=
    .resident (resources := []) result (by intro resource member; simp at member)
      (.cons (.resident (resources := []) pack (by intro resource member; simp at member)
        (.cons (.resident (resources := []) unit (by intro resource member; simp at member) .nil) .nil)) .nil)
  simpa [copiedResult, copiedPack, copiedMetadata, copiedField, metadata, Value.mapBindingOrigins,
    Value.mapFieldOrigins, BindingPack.mapOrigins, Table.get] using CopyValue.copy tree (by simp [Table.Unique])

/-- Copying the complete result changes both its owner and the nested pack's
reference to that owner. The brand and resident type stay exactly the same. -/
example {program : RuntimeProgram} :
    Copies program world .owner source destination copiedWorld := by
  exact .copy (before := world) (source := source) (destination := destination)
    (value := resultValue) (cloned := copiedResult) rfl resultInitialized
    (resultHandoffReady program .shared [destination]) (readable .shared)
    ⟨vacant,rfl,Or.inl ⟨rfl,rfl⟩⟩ ⟨0,.root (root := vacant) (id := 1) rfl rfl⟩
    (copyResult (program := program.declarations)) rfl

example : Contracts.Guard.Holds copiedWorld (.pattern 20 50 true) := by
  refine ⟨destination.child 0,copiedPack,copiedMetadata,?_,rfl,rfl,by simp [copiedMetadata]⟩
  exact ⟨{ vacant with value := some copiedResult },copiedResult,rfl,rfl,rfl,rfl,.field rfl .root⟩

example (program : Kernel.Program) : Typing.ValueTyped program copiedWorld copiedPack := by
  exact .bindings (.resident .unit rfl .nil) rfl rfl rfl (by decide)

/-- A separately copied pack still describes the originating result outside
that copied subtree; it does not invent a new result guard for its own owner. -/
example {program : Language.Program} :
    CopyValue program 30 packValue 32
      (.resident 30 packType (.bindings metadata) true [some (.resident 31 .unit .unit true [])]) := by
  obtain ⟨unit,pack,_⟩ := capabilities program
  have tree : CopyTree program 30 packValue 32
      (.resident 30 packType (.bindings metadata) true [some (.resident 31 .unit .unit true [])])
      [(11,30),(12,31)] :=
    .resident (resources := []) pack (by intro resource member; simp at member)
      (.cons (.resident (resources := []) unit (by intro resource member; simp at member) .nil) .nil)
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
