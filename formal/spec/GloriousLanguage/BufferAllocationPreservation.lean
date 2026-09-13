import GloriousLanguage.ConstructionPreservation
import GloriousLanguage.ResidentMutationPreservation
import GloriousLanguage.LoanPreservation
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
    (fun _ origin => origin.transport (World.write_locations written))
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
    (fun _ origin => origin.transport cleared.locations)
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
  have realized := typed.2.2.2.2.of_locations (World.write_locations written)
  refine ⟨well,?_,?_,?_,realized⟩
  · intro address value resident
    exact ((World.stores_typed roots (World.resident_iff_stores.mp resident)).write_vacant typed.1 vacant written).nextOwner next
  · intro id root value found contents
    by_cases live : root.live = true
    · exact (roots id root value found live contents).2
    · exact typed.2.2.1 id root value (World.write_dead_root written found live) contents
  · have locations := World.write_locations written
    apply World.root_regions_transport (after := { after with nextOwner := next }) typed.2.2.2.1 locations
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

theorem AllocatesBuffer.origin {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after) :
    pointer.Origin after := by
  cases allocated with
  | fresh =>
      intro id allocation
      have equal := Option.some.inj allocation
      subst id
      exact ⟨_,Table.get_set _ _ _,by simp,by simp⟩

theorem AllocatesBuffer.bound {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after) :
    pointer.address < 2^program.input.target.pointerBits := by
  cases allocated with
  | fresh _ extent => exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) extent.bounded

theorem AllocatesBuffer.roots {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    {id : Identity} {root : Root} (found : before.roots.get id = some root) :
    after.roots.get id = some root := by
  cases allocated
  exact (Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.root_bound valid found))).trans found

theorem AllocatesBuffer.root {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    {address : Address} {root : Root} (found : before.root address = some root) :
    after.root address = some root := by
  obtain ⟨selected,live,generation⟩ := World.root_found found
  simp [World.root,allocated.roots valid selected,live,generation]

theorem AllocatesBuffer.destinationType {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element type : Term} {count base : Nat} {pointer : RawPointer}
    {destination : Address} (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (destinationType : Execution.DestinationType before destination type) :
    Execution.DestinationType after destination type := by
  obtain ⟨whole,root,found,type,hole⟩ := destinationType
  exact ⟨whole,root,allocated.root valid found,type,hole⟩

theorem AllocatesBuffer.worldTyped {program : Kernel.Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain element count base pointer}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (buffer : AllocatesBuffer program.declarations custody before domain element count base pointer allocation after) :
    Typing.WorldTyped program after := by
  cases buffer with
  | @fresh layout request extent =>
    obtain ⟨elementLayout,elementLayoutOf,array⟩ := request.array_layout
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
      · exact ⟨by simp [regional],request.element_supported.array_count.mono (Nat.le_succ _),
          array.valid,request.size_bound,
          ⟨default,true,.array (by omega) request.count_range elementLayoutOf array⟩⟩
      · exact ⟨extent.positive,extent.aligned,extent.bounded,extent.disjoint⟩
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
    let installed : World := { initialized with nextOwner := before.nextOwner+1 }
    have atRoot : installed.root ⟨before.nextRoot,0,[]⟩ =
        some { emptyRoot with value := some shell } := by
      simp [installed,initialized,World.root,Table.get_set,emptyRoot]
    have freshPermission : Permitted installed .owner .owned ⟨before.nextRoot,0,[]⟩ := by
      refine ⟨⟨_,atRoot⟩,?_⟩
      intro identity loan selected active overlap _
      have oldFound : before.loans.get identity = some loan := selected
      obtain ⟨root,found⟩ := Option.isSome_iff_exists.mp
        (((typed.1.2.2.2.2.2.2.2.2.2.2.2.2.1 identity loan oldFound).2.2 active).2)
      have bound := World.root_bound typed.1 (World.root_found found).1
      have same : before.nextRoot = loan.referent.root := overlap.1
      exact Nat.ne_of_lt bound same.symm
    have located : installed.Located ⟨before.nextRoot,0,[]⟩ :=
      (World.Located.root_iff rfl).mpr ⟨_,atRoot⟩
    have loanTyped := installed.fresh_loan_worldTyped result freshPermission located
      (region := before.nextRegion) (by simp [installed,initialized,empty,regional]) .owning (some custody)
      (by simp [LoanKind.Allows])
    exact loanTyped

end Memory
end Glorious.Language
