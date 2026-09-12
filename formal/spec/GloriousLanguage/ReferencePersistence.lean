import GloriousLanguage.ConstructionPreservation

/-! Resident reference handles survive the real value-preserving storage
operations. These forward witnesses protect invocation loans from release;
they are not an assumption that an arbitrary loan remains active. -/
namespace Glorious.Language

theorem World.References.roots_congr {before after : World} {id : Identity}
    (roots : after.roots = before.roots) (referenced : before.References id) : after.References id := by
  simpa only [World.References,World.Resident,roots] using referenced

theorem World.References.reads {before after : World} {id : Identity}
    (reads : ∀ address, after.read address = before.read address) (referenced : before.References id) :
    after.References id := by
  obtain ⟨address,value,resident,head⟩ := referenced
  exact ⟨address,value,World.resident_iff_stores.mpr (by
    simpa only [World.Stores,reads] using World.resident_iff_stores.mp resident),head⟩

theorem World.write_retains_shell {before after : World} {mutation address : Address} {replacement : Option Value}
    {value : Value} (written : before.write mutation replacement = some after)
    (outside : ¬ mutation.Prefix address) (resident : before.Resident address value) :
    ∃ retained, after.Resident address retained ∧ retained.shell = value.shell := by
  have framed := World.write_read_shell written outside
  rw [World.resident_iff_stores.mp resident] at framed
  obtain ⟨retained,stored,same⟩ := Option.map_eq_some_iff.mp framed
  exact ⟨retained,World.resident_iff_stores.mpr stored,same⟩

theorem World.write_keeps_reference {before after : World} {mutation address : Address} {replacement : Option Value}
    {value : Value} {id : Identity} (written : before.write mutation replacement = some after)
    (outside : ¬ mutation.Prefix address) (resident : before.Resident address value) (head : value.head = .reference id) :
    ∃ retained, after.Resident address retained ∧ retained.head = .reference id := by
  obtain ⟨retained,stored,same⟩ := World.write_retains_shell written outside resident
  refine ⟨retained,stored,?_⟩
  have equal : retained.head = value.head := by
    simpa only [Value.shell,Value.withFields,Value.head] using congrArg Value.head same
  exact equal.trans head

theorem World.write_vacant_references {before after : World} {address : Address} {replacement : Option Value}
    (vacant : before.Vacant address) (written : before.write address replacement = some after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  obtain ⟨observed,value,resident,head⟩ := referenced
  have outside : ¬ address.Prefix observed := fun included =>
    vacant.not_stored ((World.resident_iff_stores.mp resident).prefix included)
  obtain ⟨retained,stored,head⟩ := World.write_keeps_reference written outside resident head
  exact ⟨observed,retained,stored,head⟩

/-- Replacing a non-reference shell whose fields have all been consumed
cannot destroy any reference guard. The actual field premises matter even
when the retained representation has nonzero arity. -/
theorem World.write_nonreference_shell_references {before after : World} {address : Address}
    {value : Value} {replacement : Option Value}
    (stored : before.Stores address value) (fields : ∀ field ∈ value.fields, field = none)
    (notReference : ∀ id, value.head ≠ .reference id)
    (written : before.write address replacement = some after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  obtain ⟨observed,reference,resident,head⟩ := referenced
  have outside : ¬ address.Prefix observed := by
    intro included
    obtain ⟨suffix,equal⟩ := Address.prefix_extension included
    have nested := World.resident_iff_stores.mp resident
    change before.read observed = some reference at nested
    rw [equal,World.read_append,stored] at nested
    cases suffix with
    | nil =>
      have same : value = reference := Option.some.inj nested
      exact notReference id (same ▸ head)
    | cons index rest =>
      change value.atPath (index :: rest) = some reference at nested
      obtain ⟨child,selected,_⟩ := Option.bind_eq_some_iff.mp nested
      have slot : value.fields[index]? = some (some child) := by
        cases found : value.fields[index]? <;> simp_all
      have empty := fields (some child) (List.mem_of_getElem? slot)
      cases empty
  obtain ⟨retained,present,head⟩ := World.write_keeps_reference written outside resident head
  exact ⟨observed,retained,present,head⟩

theorem World.write_nonreference_leaf_references {before after : World} {address : Address}
    {value : Value} {replacement : Option Value}
    (stored : before.Stores address value) (fields : value.fields = [])
    (notReference : ∀ id, value.head ≠ .reference id)
    (written : before.write address replacement = some after)
    {id : Identity} (referenced : before.References id) : after.References id :=
  World.write_nonreference_shell_references stored (by simp [fields]) notReference written referenced

theorem Allocates.references {program : Program} {before after : World}
    {home region type layout mutable address originBound} (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after)
    {id : Identity} (referenced : before.References id) : after.References id :=
  referenced.reads (allocated.read valid)

theorem Transfers.references {program : RuntimeProgram} {before after : World} {authority source destination}
    (transferred : Transfers program before authority source destination after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  obtain ⟨address,value,resident,head⟩ := referenced
  cases transferred with
  | move stored _ _ _ vacant separate _ cleared written =>
    by_cases included : source.Prefix address
    · obtain ⟨suffix,equal⟩ := Address.prefix_extension included
      have nested := World.resident_iff_stores.mp resident
      change before.read address = some value at nested
      rw [equal,World.read_append,stored] at nested
      refine ⟨{ destination with fields := destination.fields ++ suffix },value,World.resident_iff_stores.mpr ?_,head⟩
      change _ = some value
      rw [World.write_read_inside written suffix]
      exact nested
    · obtain ⟨retained,present,head⟩ := World.write_keeps_reference cleared included resident head
      exact World.write_vacant_references (vacant.clear cleared (fun inside => separate inside.1.overlaps)) written
        ⟨address,retained,present,head⟩

theorem FormsLoan.references {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  cases borrowed with
  | borrow _ _ _ _ _ _ _ vacant _ _ written =>
    exact (World.write_vacant_references vacant written referenced).roots_congr rfl

theorem FormsLoan.region_live {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    region ∈ after.liveRegions := by
  cases borrowed with
  | borrow _ _ _ live _ _ _ _ _ _ written =>
    have same := congrArg World.liveRegions (World.write_rest written)
    simpa only [same] using live

/-- The handle and loan record come from the same actual formation write.
All invocation and source-reference witnesses project this single product. -/
theorem FormsLoan.created_handle {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    ∃ type, after.Stores destination (.resident before.nextOwner (.reference mode (.runtimeRegion region) type)
      (.reference before.nextLoan) true []) ∧
      after.loans.get before.nextLoan = some ⟨before.nextLoan,authority.parentLoan,referent,mode,region,true,purpose.kind,authority.guardLoans before,false,none⟩ := by
  cases borrowed with
  | @borrow original middle parent _ _ _ _ _ _ _ _ _ parentEq written =>
    refine ⟨original.type,?_,?_⟩
    · change middle.read destination = some _
      simpa [Value.atPath] using World.write_read_inside written []
    · rw [Table.get_set,parentEq]

theorem FormsLoan.created_reference {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    after.References before.nextLoan := by
  obtain ⟨type,stored,_⟩ := borrowed.created_handle
  exact ⟨destination,_,World.resident_iff_stores.mpr stored,rfl⟩

theorem Copies.references {program : RuntimeProgram} {before after : World} {authority source destination}
    (copied : Copies program before authority source destination after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  cases copied with
  | copy _ _ _ _ vacant _ _ written =>
    exact (World.write_vacant_references vacant written referenced).roots_congr rfl

theorem Acquires.references {program : RuntimeProgram} {before after : World} {authority force source destination}
    (acquired : Acquires program before authority force source destination after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  cases acquired with
  | explicitMove transferred => exact transferred.references referenced
  | copy copied => exact copied.references referenced
  | move _ _ _ transferred => exact transferred.references referenced

theorem Clears.keeps_reference {before after : World} {mutations : List Address} {address : Address} {value : Value} {id : Identity}
    (cleared : Clears before mutations after) (outside : ∀ mutation ∈ mutations, ¬ mutation.Prefix address)
    (resident : before.Resident address value) (head : value.head = .reference id) :
    ∃ retained, after.Resident address retained ∧ retained.head = .reference id := by
  induction cleared generalizing value with
  | nil => exact ⟨value,resident,head⟩
  | cons written _ ih =>
    obtain ⟨retained,present,head⟩ := World.write_keeps_reference written (outside _ List.mem_cons_self) resident head
    exact ih (fun mutation member => outside mutation (List.mem_cons_of_mem _ member)) present head

theorem ListRel.get_left {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right) {index : Nat} {value : α} (found : left[index]? = some value) :
    ∃ result, right[index]? = some result ∧ relation value result := by
  induction related generalizing index with
  | nil => simp at found
  | cons relation rest ih =>
    cases index with
    | zero => cases Option.some.inj found; exact ⟨_,rfl,relation⟩
    | succ index => exact ih found

theorem NewValue.references {program : RuntimeProgram} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  obtain ⟨address,value,resident,atHead⟩ := referenced
  cases constructed with
  | construct vacant _ ready disjoint cleared written =>
    have inputs := ready.1
    by_cases moved : ∃ source ∈ sources, source.address.Prefix address
    · obtain ⟨source,member,included⟩ := moved
      obtain ⟨index,bound,atSource⟩ := List.mem_iff_getElem.mp member
      have found : sources[index]? = some source := by rw [List.getElem?_eq_getElem bound,atSource]
      obtain ⟨original,atValue,stored⟩ := inputs.get_left found
      obtain ⟨suffix,equal⟩ := Address.prefix_extension included
      have nested := World.resident_iff_stores.mp resident
      change before.read address = some value at nested
      rw [equal,World.read_append,stored] at nested
      refine ⟨{ destination with fields := destination.fields ++ index :: suffix },value,World.resident_iff_stores.mpr ?_,atHead⟩
      have inserted := World.write_read_inside written (index :: suffix)
      apply Eq.trans inserted
      simpa [Value.atPath,Value.fields,atValue] using nested
    · have outside : ∀ mutation ∈ sources.map ResolvedPlace.address, ¬ mutation.Prefix address := by
        intro mutation member included
        obtain ⟨source,present,rfl⟩ := List.mem_map.mp member
        exact moved ⟨source,present,included⟩
      obtain ⟨retained,present,head⟩ := cleared.keeps_reference outside resident atHead
      have stillVacant := cleared.vacant vacant (by
        intro mutation member included
        obtain ⟨source,present,rfl⟩ := List.mem_map.mp member
        exact disjoint source present included.1.overlaps)
      exact (World.write_vacant_references stillVacant written ⟨address,retained,present,head⟩).roots_congr rfl

theorem Retires.references {before after : World} {root id : Identity}
    (retired : Retires before root after) (referenced : before.References id) : after.References id :=
  referenced.reads retired.read

end Glorious.Language
