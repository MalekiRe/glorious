import GloriousLanguage.ConstructionPreservation
import GloriousLanguage.LocalPreservation
import GloriousLanguage.TargetLayoutValidity

/-! Storage preservation for the actual raw-memory producers. Bulk relocation
keeps one evaluated source snapshot through clearing and typed installation;
source/destination overlap does not duplicate the transported owner trees. -/
namespace Glorious.Language

theorem Typing.ValueTyped.write_vacant {program : Kernel.Program} {before after : World}
    {destination : Address} {inserted value : Value}
    (valid : before.WellFormed) (vacant : before.Vacant destination)
    (written : before.write destination (some inserted) = some after)
    (typed : Typing.ValueTyped program before value) : Typing.ValueTyped program after value := by
  have proofs := congrArg World.availability (World.write_rest written)
  apply typed.transport (after := after) ?_ proofs
    (fun _ origin => origin.write written)
  intro id loan found active
  exact ⟨by simpa only [World.write_loans written] using found,fun type located =>
    (World.write_address_types written (vacant.no_located_descendant
      (World.liveLoanLocations valid _ _ found active))).mp located⟩

theorem Clears.valueTyped {program : Kernel.Program} {before after : World} {addresses : List Address} {value : Value}
    (valid : before.WellFormed)
    (allowed : ∀ address ∈ addresses, ∃ authority, Permitted before authority .owned address)
    (cleared : Clears before addresses after) (typed : Typing.ValueTyped program before value) :
    Typing.ValueTyped program after value := by
  have proofs := congrArg World.availability cleared.rest
  apply typed.transport (after := after) ?_ proofs
    (fun _ origin => origin.clear cleared)
  intro id loan found active
  refine ⟨by simpa only [cleared.loans] using found,?_⟩
  intro type located
  apply cleared.address_type located
  intro address member
  obtain ⟨authority,permission⟩ := allowed address member
  exact permission.owned_no_loan_descendant (World.loanParents valid) found active

theorem Typing.ValueTyped.nextOwner {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) (next : Nat) :
    Typing.ValueTyped program { world with nextOwner := next } value := by
  apply typed.transport (after := { world with nextOwner := next }) ?_ rfl ?_
  · intro id loan found live
    exact ⟨found,fun type located => located.retained (fun _ selected => selected) (fun _ => rfl)⟩
  · intro pointer origin
    exact origin

/-- Insertion consumes facts about the actual detached input tree. Bulk moves
derive them from evaluated source owners; allocation derives them from its
fresh uninitialized shell. Neither consumer supplies post-state typing. -/
theorem World.install_worldTyped {program : Kernel.Program} {before after : World}
    {destination : Address} {inserted : Value} {next : Nat}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before) (vacant : before.Vacant destination)
    (located : AddressType program.declarations before destination inserted.type)
    (checked : Typing.ValueTyped program before inserted)
    (monotone : before.nextOwner ≤ next)
    (owners : ∀ path value, ResidentAt inserted path value → value.owner < next)
    (unique : ∀ a b x y, ResidentAt inserted a x → ResidentAt inserted b y → x.owner = y.owner → a = b)
    (separate : ∀ path value, ResidentAt inserted path value →
      ∀ address original, before.Resident address original → value.owner ≠ original.owner)
    (packs : ∀ path value pack, ResidentAt inserted path value → value.head = .bindings pack →
      pack.brand < before.nextProof ∧ pack.region ∈ before.liveRegions ∧ pack.fields.length = value.fields.length ∧
      pack.fields.Nodup ∧ ∀ fact ∈ pack.facts, fact.resultOrigin < next)
    (references : ∀ path value id, ResidentAt inserted path value → value.head = .reference id →
      ∃ loan, before.loans.get id = some loan ∧ loan.live = true)
    (written : before.write destination (some inserted) = some after) :
    Typing.WorldTyped program { after with nextOwner := next } := by
  have well := World.install_wellFormed typed.1 vacant monotone owners unique separate packs references written
  obtain ⟨offset,located⟩ := located
  have roots := World.write_typed_roots valid inventory typed.roots located written
    (fun value same => by cases Option.some.inj same; exact ⟨checked,rfl⟩)
  refine ⟨well,?_,?_,?_⟩
  · intro address value resident
    exact ((World.stores_typed roots (World.resident_iff_stores.mp resident)).write_vacant typed.1 vacant written).nextOwner next
  · intro id root value found contents
    by_cases live : root.live = true
    · exact (roots id root value found live contents).2
    · exact typed.2.2.1 id root value (World.write_dead_root written found live) contents
  · have locations := World.write_locations written
    apply World.root_regions_transport (after := { after with nextOwner := next }) typed.2.2.2 locations
    exact Nat.le_of_eq (congrArg World.nextRegion (World.write_rest written)).symm

theorem World.install_owned_worldTyped {program : Kernel.Program} {before after : World}
    {destination : Address} {inserted : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before) (vacant : before.Vacant destination)
    (located : AddressType program.declarations before destination inserted.type)
    (checked : Typing.ValueTyped program before inserted)
    (owners : ∀ path value, ResidentAt inserted path value → value.owner < before.nextOwner)
    (unique : ∀ a b x y, ResidentAt inserted a x → ResidentAt inserted b y → x.owner = y.owner → a = b)
    (separate : ∀ path value, ResidentAt inserted path value →
      ∀ address original, before.Resident address original → value.owner ≠ original.owner)
    (packs : ∀ path value pack, ResidentAt inserted path value → value.head = .bindings pack →
      pack.brand < before.nextProof ∧ pack.region ∈ before.liveRegions ∧ pack.fields.length = value.fields.length ∧
      pack.fields.Nodup ∧ ∀ fact ∈ pack.facts, fact.resultOrigin < before.nextOwner)
    (references : ∀ path value id, ResidentAt inserted path value → value.head = .reference id →
      ∃ loan, before.loans.get id = some loan ∧ loan.live = true)
    (written : before.write destination (some inserted) = some after) : Typing.WorldTyped program after := by
  have result := World.install_worldTyped valid inventory typed vacant located checked
    (Nat.le_refl _) owners unique separate packs references written
  have counter := congrArg World.nextOwner (World.write_rest written)
  have same : ({ after with nextOwner := before.nextOwner } : World) = after := by rw [← counter]
  rw [same] at result
  exact result

theorem Term.RuntimeRegionsBelow.array_count {element : Term} {bound count : Nat}
    (supported : element.RuntimeRegionsBelow bound) :
    (Term.array element (.constant (.integer false .pointer count))).RuntimeRegionsBelow bound := by
  intro id occurs
  cases occurs with
  | child member nested =>
    simp only [Term.children,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact supported id nested
    · cases nested with
      | child member _ => simp [Term.children] at member

theorem Typing.FieldsTyped.holes {program : Kernel.Program} {world : World} (element : Term) (count : Nat) :
    Typing.FieldsTyped program world (List.replicate count none) (List.replicate count element) := by
  induction count with
  | zero => exact .nil
  | succ count ih => simpa only [List.replicate_succ] using Typing.FieldsTyped.hole ih

theorem ResidentAt.holes {owner : Identity} {type : Term} {head : ValueHead} {live : Bool} {count : Nat}
    {path : List Nat} {value : Value}
    (inside : ResidentAt (.resident owner type head live (List.replicate count none)) path value) :
    path = [] ∧ value = .resident owner type head live (List.replicate count none) := by
  cases inside with
  | root => exact ⟨rfl,rfl⟩
  | field selected _ =>
    simp only [Value.fields,List.getElem?_replicate] at selected
    split at selected <;> cases selected

theorem Table.set_set {α : Type} (table : Table α) (id : Identity) (first second : α) :
    (table.set id first).set id second = table.set id second := by
  simp [Table.set,Table.erase,List.filter_filter]

namespace Memory

theorem AllocatesBuffer.worldTyped {program : Kernel.Program} {before after : World}
    {domain element count base pointer}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (buffer : AllocatesBuffer program.declarations before domain element count base pointer after) :
    Typing.WorldTyped program after := by
  cases buffer with
  | @fresh elementLayout layout domainValid supported countRange elementLayoutOf array maximum positive aligned extent disjoint =>
    let regional : World := { before with liveRegions := before.nextRegion :: before.liveRegions, nextRegion := before.nextRegion+1 }
    have fresh : FreshRegion before before.nextRegion regional := ⟨rfl,rfl⟩
    have regionalTyped := fresh.worldTyped typed
    let type : Term := .array element (.constant (.integer false .pointer count))
    let shell : Value := .resident before.nextOwner type .array false (List.replicate count none)
    let emptyRoot : Root := ⟨.allocation domain,0,before.nextRegion,base,layout,type,none,true,before.clock,true,List.replicate layout.size none⟩
    let empty : World := { regional with roots := before.roots.set before.nextRoot emptyRoot, nextRoot := before.nextRoot+1,clock := before.clock+1 }
    have allocated : Allocates program.declarations regional (.allocation domain) before.nextRegion type layout true
        ⟨before.nextRoot,0,[]⟩ empty := by
      apply Allocates.fresh
      · simp [regional]
      · exact supported.array_count.mono (Nat.le_succ _)
      · exact array.valid
      · exact maximum
      · exact ⟨⟨[],[],0,default,true,{}⟩,.array (by omega) countRange elementLayoutOf array⟩
      · exact positive
      · exact aligned
      · exact extent
      · exact disjoint
    have emptyTyped := allocated.worldTyped regionalTyped
    have rootFound : empty.root ⟨before.nextRoot,0,[]⟩ = some emptyRoot := by
      simp [empty,World.root,Table.get_set,emptyRoot]
    have vacant : empty.Vacant ⟨before.nextRoot,0,[]⟩ := ⟨emptyRoot,rootFound,Or.inl ⟨rfl,rfl⟩⟩
    have located : AddressType program.declarations empty ⟨before.nextRoot,0,[]⟩ type :=
      ⟨0,.root (root := emptyRoot) (Table.get_set _ _ _) rfl⟩
    have shellTyped : Typing.ValueTyped program empty shell := by
      apply Typing.ValueTyped.aggregate ?_ (Typing.FieldsTyped.holes element count)
      exact Or.inr (Or.inl ⟨element,false,.pointer,(count : Int),rfl,rfl,rfl,by simp,
        fun field member => List.eq_of_mem_replicate member⟩)
    let initialized : World := { empty with roots := before.roots.set before.nextRoot { emptyRoot with value := some shell } }
    have written : empty.write ⟨before.nextRoot,0,[]⟩ (some shell) = some initialized := by
      simp [World.write,rootFound,empty,initialized,Table.set_set]
    have result : Typing.WorldTyped program { initialized with nextOwner := before.nextOwner+1 } := by
      apply World.install_worldTyped (inserted := shell) valid inventory emptyTyped vacant located shellTyped (Nat.le_succ _)
        ?_ ?_ ?_ ?_ ?_ written
      · intro path value inside
        obtain ⟨rfl,rfl⟩ := inside.holes
        exact Nat.lt_succ_self _
      · intro first second left right one two same
        obtain ⟨rfl,rfl⟩ := one.holes
        exact two.holes.1.symm
      · intro path value inside address original stored same
        obtain ⟨rfl,rfl⟩ := inside.holes
        have bound := World.owner_bound emptyTyped.1 stored
        change original.owner < before.nextOwner at bound
        change before.nextOwner = original.owner at same
        rw [same] at bound
        exact Nat.lt_irrefl _ bound
      · intro path value pack inside head
        obtain ⟨rfl,rfl⟩ := inside.holes
        cases head
      · intro path value id inside head
        obtain ⟨rfl,rfl⟩ := inside.holes
        cases head
    exact result

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

theorem StoresPointer.worldTyped {program : Kernel.Program} {before after : World} {destination mode type pointer}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : pointer.address < 2^program.declarations.input.target.pointerBits) (origin : pointer.Origin before)
    (stored : StoresPointer program before destination mode type pointer after) : Typing.WorldTyped program after :=
  stored.2.empty_worldTyped valid inventory typed (by simp) (by simp) (.pointer bound origin)

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
