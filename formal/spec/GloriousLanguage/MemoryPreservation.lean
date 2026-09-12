import GloriousLanguage.BufferAllocationPreservation
import GloriousLanguage.PointerStorageConstruction
import GloriousLanguage.LocalPreservation

/-! Storage preservation for the actual raw-memory producers. The common
buffer allocator and pointer installer supply their lower proofs; bulk moves,
raw operations and primitive execution consume those same producers. -/
namespace Glorious.Language
namespace Memory

theorem InstallsResidents.rest {program : Program} {before after : World} {addresses : List Address} {values : List (Option Value)}
    (installed : InstallsResidents program before addresses values after) : after = { before with roots := after.roots } := by
  induction installed with
  | nil => rfl
  | hole _ _ ih => exact ih
  | resident _ _ written _ ih =>
    have first := World.write_rest written
    conv => lhs; rw [ih,first]

theorem InstallsResidents.locations {program : Program} {before after : World} {addresses : List Address} {values : List (Option Value)}
    (installed : InstallsResidents program before addresses values after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  induction installed with
  | nil => rfl
  | hole _ _ ih => exact ih
  | resident _ _ written _ ih => exact ih.trans (World.write_locations written id)

theorem InstallsResidents.worldTyped {program : Kernel.Program} {before after : World}
    {addresses : List Address} {values : List (Option Value)}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (checked : ∀ (index : Nat) value, values[index]? = some (some value) → Typing.ValueTyped program before value)
    (owners : ∀ (index : Nat) value, values[index]? = some (some value) →
      ∀ path resident, ResidentAt value path resident → resident.owner < before.nextOwner)
    (unique : ∀ (first second : Nat) left right x y a b,
      values[first]? = some (some x) → values[second]? = some (some y) →
      ResidentAt x left a → ResidentAt y right b → a.owner = b.owner → first = second ∧ left = right)
    (separate : ∀ (index : Nat) value, values[index]? = some (some value) →
      ∀ path resident, ResidentAt value path resident →
        ∀ address original, before.Resident address original → resident.owner ≠ original.owner)
    (packs : ∀ (index : Nat) value, values[index]? = some (some value) →
      ∀ path resident pack, ResidentAt value path resident → resident.head = .bindings pack →
        pack.brand < before.nextProof ∧ pack.region ∈ before.liveRegions ∧ pack.fields.length = resident.fields.length ∧
        pack.fields.Nodup ∧ ∀ fact ∈ pack.facts, fact.resultOrigin < before.nextOwner)
    (references : ∀ (index : Nat) value, values[index]? = some (some value) →
      ∀ path resident id, ResidentAt value path resident → resident.head = .reference id →
        ∃ loan, before.loans.get id = some loan ∧ loan.live = true)
    (installed : InstallsResidents program.declarations before addresses values after) : Typing.WorldTyped program after := by
  induction installed with
  | nil => exact typed
  | hole vacant rest ih =>
    exact ih typed (fun index value found => checked (index+1) value found)
      (fun index value found => owners (index+1) value found)
      (fun first second left right x y a b one two inside nested same => by
        obtain ⟨indices,paths⟩ := unique (first+1) (second+1) left right x y a b one two inside nested same
        exact ⟨Nat.add_right_cancel indices,paths⟩)
      (fun index value found => separate (index+1) value found)
      (fun index value found => packs (index+1) value found)
      (fun index value found => references (index+1) value found)
  | @resident before destination addresses value values middle after vacant located written rest ih =>
    have middleTyped := World.install_owned_worldTyped valid inventory typed vacant located (checked 0 value rfl)
      (owners 0 value rfl)
      (fun a b x y first second same => (unique 0 0 a b value value x y rfl rfl first second same).2)
      (separate 0 value rfl) (packs 0 value rfl) (references 0 value rfl) written
    have first := World.write_rest written
    have counter := congrArg World.nextOwner first
    have proofs := congrArg World.nextProof first
    have regions := congrArg World.liveRegions first
    have loans := congrArg World.loans first
    apply ih middleTyped
    · intro index resident found
      exact (checked (index+1) resident found).write_vacant typed.1 vacant written
    · intro index resident found path nested inside
      simpa only [counter] using owners (index+1) resident found path nested inside
    · intro first second left right x y a b one two inside nested same
      obtain ⟨indices,paths⟩ := unique (first+1) (second+1) left right x y a b one two inside nested same
      exact ⟨Nat.add_right_cancel indices,paths⟩
    · intro index resident found path nested inside address original stored same
      rcases World.write_value_origin written stored with ⟨suffix,_,inFirst⟩ | ⟨old,oldFound,shell⟩
      · have impossible := (unique (index+1) 0 path suffix resident value nested original found rfl inside inFirst same).1
        omega
      · have ownersEq : original.owner = old.owner := by
          simpa only [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shell
        exact separate (index+1) resident found path nested inside address old oldFound (same.trans ownersEq)
    · intro index resident found path nested pack inside head
      simpa only [proofs,regions,counter] using packs (index+1) resident found path nested pack inside head
    · intro index resident found path nested id inside head
      simpa only [loans] using references (index+1) resident found path nested id inside head

theorem BulkMove.worldTyped {program : Kernel.Program} {before after : World} {sources destinations : List Address}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (moved : BulkMove program.declarations before sources destinations after) : Typing.WorldTyped program after := by
  obtain ⟨values,middle,length,sourceApart,destinationApart,inputs,permissions,vacant,cleared,installed⟩ := moved
  have allowed : ∀ address ∈ sources, ∃ authority, Permitted before authority .owned address :=
    fun address member => ⟨.owner,permissions address member⟩
  have middleTyped := cleared.worldTyped typed allowed
  have counter := congrArg World.nextOwner cleared.rest
  have proofs := congrArg World.nextProof cleared.rest
  have regions := congrArg World.liveRegions cleared.rest
  have input : ∀ (index : Nat) value, values[index]? = some (some value) →
      ∃ source, sources[index]? = some source ∧ before.Stores source value := by
    intro index value found
    exact inputs.get_right found
  apply installed.worldTyped valid inventory middleTyped
  · intro index value found
    obtain ⟨source,_,stored⟩ := input index value found
    exact cleared.valueTyped typed.1 allowed (World.stores_typed typed.roots stored)
  · intro index value found path resident inside
    obtain ⟨source,_,stored⟩ := input index value found
    simpa only [counter] using World.owner_bound typed.1 (stored.residentAt inside)
  · intro first second left right x y a b one two inside nested same
    obtain ⟨firstSource,firstFound,firstStored⟩ := input first x one
    obtain ⟨secondSource,secondFound,secondStored⟩ := input second y two
    have addressEq := typed.1.2.2.2.2.2.2.2.1 _ _ a b
      (firstStored.residentAt inside) (secondStored.residentAt nested) same
    by_cases indices : first = second
    · subst second
      have sourceEq := Option.some.inj (firstFound.symm.trans secondFound)
      subst secondSource
      exact ⟨rfl,List.append_cancel_left (congrArg Address.fields addressEq)⟩
    · have apart := sourceApart.get_other (fun different overlap => different overlap.symm) firstFound secondFound indices
      apply False.elim
      apply apart
      apply Address.Prefix.overlap_of_common (common := { firstSource with fields := firstSource.fields ++ left })
      · exact ⟨rfl,rfl,left,rfl⟩
      · rw [addressEq]
        exact ⟨rfl,rfl,right,rfl⟩
  · intro index value found path resident inside address original current same
    obtain ⟨source,sourceFound,stored⟩ := input index value found
    obtain ⟨old,oldFound,shell⟩ := cleared.resident_origin current
    have ownerEq : original.owner = old.owner := by
      simpa only [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shell
    have addressEq := typed.1.2.2.2.2.2.2.2.1 _ _ resident old (stored.residentAt inside) oldFound (same.trans ownerEq)
    have absent := cleared.cleared (List.mem_of_getElem? sourceFound) path
    rw [addressEq,World.resident_iff_stores.mp current] at absent
    cases absent
  · intro index value found path resident pack inside head
    obtain ⟨source,_,stored⟩ := input index value found
    simpa only [proofs,regions,counter] using
      typed.1.2.2.2.2.2.1 _ resident pack (stored.residentAt inside) head
  · intro index value found path resident id inside head
    obtain ⟨source,_,stored⟩ := input index value found
    simpa only [cleared.loans] using
      typed.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ resident id (stored.residentAt inside) head

theorem ReallocatesBuffer.worldTyped {program : Kernel.Program} {before after : World}
    {old domain element count base result}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (reallocated : ReallocatesBuffer program.declarations before old domain element count base result after) :
    Typing.WorldTyped program after := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,allocated,_,moved,released⟩ := reallocated
  exact released.worldTyped (moved.worldTyped valid inventory (allocated.worldTyped valid inventory typed))

theorem RawRead.worldTyped {program : Kernel.Program} {before after : World}
    {pointer type copy destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (read : RawRead program.declarations before pointer type copy destination after) : Typing.WorldTyped program after := by
  cases read with
  | read _ _ _ copied =>
    rcases copied with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.worldTyped valid inventory typed
    · exact moved.worldTyped valid inventory typed

theorem RawWrite.worldTyped {program : Kernel.Program} {before after : World}
    {authority source pointer type}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (written : RawWrite program.declarations before authority source pointer type after) : Typing.WorldTyped program after := by
  cases written with
  | write _ _ _ _ _ moved => exact moved.worldTyped valid inventory typed

theorem RawBorrow.worldTyped {program : Kernel.Program} {before after : World}
    {pointer type mode region destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (borrowed : RawBorrow program.declarations before pointer type mode region destination after) : Typing.WorldTyped program after := by
  cases borrowed with
  | borrow _ _ _ _ borrowed => exact borrowed.worldTyped valid inventory typed

end Memory

namespace Execution

theorem StoresScalar.worldTyped {program : Kernel.Program} {before after : World} {destination scalar}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (stored : StoresScalar program before destination scalar after) : Typing.WorldTyped program after :=
  stored.2.2.empty_worldTyped valid inventory typed (by simp) (by simp) (.scalar stored.1)

theorem StoresUnit.worldTyped {program : Kernel.Program} {before after : World} {destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (stored : StoresUnit program before destination after) : Typing.WorldTyped program after :=
  stored.2.empty_worldTyped valid inventory typed (by simp) (by simp) .unit


/-- Every primitive transition preserves complete storage typing, including
fresh buffers, overlapping bulk relocation, raw reference operations and
layout results. Arithmetic result validity is consumed from StoresScalar's
actual producer contract; arithmetic totality is proved independently. -/
theorem PrimitiveStep.worldTyped {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (step : PrimitiveStep program before event after) :
    Typing.WorldTyped program after.world := by
  cases step with
  | scalar task primitive inputs calculated stored => exact stored.worldTyped valid inventory typed
  | scalarFault => exact typed
  | allocate task primitive domain count nonnegative allocated stored =>
    exact stored.worldTyped valid inventory (allocated.worldTyped valid inventory typed) allocated.bound allocated.origin
  | release task primitive domain pointer released stored =>
    exact stored.worldTyped valid inventory (released.worldTyped typed)
  | reallocate task primitive domain old count nonnegative reallocated stored =>
    exact stored.worldTyped valid inventory (reallocated.worldTyped valid inventory typed) reallocated.bound reallocated.origin
  | rawRead task primitive pointer read => exact read.worldTyped valid inventory typed
  | rawCopy task primitive pointer read => exact read.worldTyped valid inventory typed
  | rawWrite task primitive pointer written stored =>
    exact stored.worldTyped valid inventory (written.worldTyped valid inventory typed)
  | rawBorrow task primitive pointer borrowed => exact borrowed.worldTyped valid inventory typed
  | pointerOffset task primitive pointer amount offset stored =>
    exact stored.worldTyped valid inventory typed offset.bound offset.origin
  | pointerAddress task primitive pointer stored => exact stored.worldTyped valid inventory typed
  | pointerWithAddress task primitive pointer integer nonnegative changed stored =>
    exact stored.worldTyped valid inventory typed changed.bound changed.origin
  | layout task primitive layout constant destination written counter =>
    subst counter
    exact constant.install_worldTyped valid inventory typed destination.vacant destination.addressType written
  | abort => exact typed

end Execution

end Glorious.Language
