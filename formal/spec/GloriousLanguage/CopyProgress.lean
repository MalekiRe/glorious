import GloriousLanguage.CopyResourcePreservation
import GloriousLanguage.CopyPreservation
import GloriousLanguage.DropCapabilities
import GloriousLanguage.StorageWrites
import GloriousLanguage.AllocationPreservation
import GloriousLanguage.AllocationOutcomes

/-! Source duplication capability and actual closed initialized storage
construct the one Copy traversal and its fresh owner-origin table. The
ordinary storage consumers use that construction, not a completed-copy or
typed-post-world admission premise. -/
namespace Glorious.Language

theorem Principal.duplicable_restricts {principal : Principal} (ordered : Principal.duplicable.Restricts principal) :
    principal = .duplicable := by
  have twice := ordered 2 True.intro
  cases principal <;> simp_all [Principal.Permits]

theorem Value.InvariantClosed.copy_resources {program : RuntimeProgram} {world : World} {value : Value}
    (valid : world.WellFormed) (closed : value.InvariantClosed program world)
    (capability : PrincipalOf program.declarations value.type .duplicable) :
    ∀ binding ∈ value.resources, binding.ReadOnly := by
  unfold Value.InvariantClosed at closed
  cases type : value.type with
  | nominal identity arguments =>
      simp only [type] at closed
      obtain ⟨data,_,declared⟩ := closed
      cases invariant : data.invariant with
      | none => simp only [invariant] at declared; simp [declared]
      | some invariant =>
          simp only [invariant] at declared
          obtain ⟨contract,_,_,holds⟩ := declared
          exact contract.copyResources world value valid holds capability
  | _ => simp only [type] at closed; simp [closed]

theorem Typing.ValueTyped.copy_residents {program : Kernel.Program} {world : World} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (well : world.WellFormed) (typed : Typing.ValueTyped program world value)
    (closed : value.ResourcesClosed program world) (capability : PrincipalOf program.declarations value.type .duplicable) :
    ∀ path resident, ResidentAt value path resident →
      PrincipalOf program.declarations resident.type .duplicable ∧ ∀ binding ∈ resident.resources, binding.ReadOnly := by
  intro path resident inside
  obtain ⟨principal,selected,restriction⟩ := typed.resident_capability valid inventory capability inside
  have same := Principal.duplicable_restricts restriction
  subst principal
  exact ⟨selected,((closed resident .owner .shared (.resident inside)).2).copy_resources well selected⟩

theorem CopyFields.exists {program : Program} {fields : List (Option Value)}
    (present : ∀ field ∈ fields, field.isSome = true)
    (children : ∀ child, some child ∈ fields → ∀ next, ∃ finish copied origins,
      CopyTree program next child finish copied origins) (next : Nat) :
    ∃ finish copied origins, CopyFields program next fields finish copied origins := by
  induction fields generalizing next with
  | nil => exact ⟨next,[],[],.nil⟩
  | cons field rest ih =>
      cases field with
      | none => have impossible := present none List.mem_cons_self; cases impossible
      | some value =>
          obtain ⟨middle,copied,first,copy⟩ := children value List.mem_cons_self next
          obtain ⟨finish,copies,later,tail⟩ := ih
            (fun field member => present field (List.mem_cons_of_mem _ member))
            (fun child member => children child (List.mem_cons_of_mem _ member)) middle
          exact ⟨finish,some copied :: copies,first ++ later,.cons copy tail⟩

theorem CopyTree.exists {program : Program} {value : Value}
    (initialized : value.Initialized)
    (admitted : ∀ path resident, ResidentAt value path resident →
      PrincipalOf program resident.type .duplicable ∧ ∀ binding ∈ resident.resources, binding.ReadOnly)
    (next : Nat) : ∃ finish copied origins, CopyTree program next value finish copied origins := by
  have children : ∀ child, some child ∈ value.fields → ∀ first, ∃ finish copied origins,
      CopyTree program first child finish copied origins := by
    intro child member first
    obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
    have inside : ResidentAt value [index] child := .field found .root
    exact CopyTree.exists (initialized.resident inside)
      (fun path resident nested => admitted _ resident (inside.append nested)) first
  obtain ⟨live,present⟩ := initialized [] value .root
  obtain ⟨capability,shared⟩ := admitted [] value .root
  obtain ⟨finish,copies,origins,fields⟩ := CopyFields.exists present children (next+1)
  cases value with
  | resident owner type head shell fields resources =>
      change shell = true at live
      subst shell
      exact ⟨finish,.resident next type head true copies resources,(owner,next) :: origins,.resident capability shared fields⟩
termination_by value
decreasing_by exact Value.field_sizeOf member

theorem CopyTree.source_owner {program : Program} {next finish : Nat} {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins) :
    ∀ owner fresh, (owner,fresh) ∈ origins → ∃ path resident, ResidentAt value path resident ∧ resident.owner = owner := by
  refine CopyTree.rec
    (motive_1 := fun _ value _ _ origins _ => ∀ owner fresh, (owner,fresh) ∈ origins →
      ∃ path resident, ResidentAt value path resident ∧ resident.owner = owner)
    (motive_2 := fun _ fields _ _ origins _ => ∀ owner fresh, (owner,fresh) ∈ origins →
      ∃ (index : Nat) (child : Value) (path : List Nat) (resident : Value),
        fields[index]? = some (some child) ∧ ResidentAt child path resident ∧ resident.owner = owner)
    ?_ ?_ ?_ copy
  · intro next owner type head fields resources copied finish origins _ _ _ ih id fresh member
    rcases List.mem_cons.mp member with equal | later
    · cases equal; exact ⟨[],_,.root,rfl⟩
    · obtain ⟨index,child,path,resident,found,inside,same⟩ := ih id fresh later
      exact ⟨index :: path,resident,.field found inside,same⟩
  · intro next owner fresh member; cases member
  · intro next middle finish value copied rest copies first later _ _ ih tail owner fresh member
    rcases List.mem_append.mp member with earlier | later
    · obtain ⟨path,resident,inside,same⟩ := ih owner fresh earlier
      exact ⟨0,value,path,resident,rfl,inside,same⟩
    · obtain ⟨index,child,path,resident,found,inside,same⟩ := tail owner fresh later
      exact ⟨index+1,child,path,resident,found,inside,same⟩

theorem CopyFields.source_owner {program : Program} {next finish : Nat}
    {fields copied : List (Option Value)} {origins : Table Identity}
    (copy : CopyFields program next fields finish copied origins) :
    ∀ owner fresh, (owner,fresh) ∈ origins →
      ∃ (index : Nat) (child : Value) (path : List Nat) (resident : Value),
        fields[index]? = some (some child) ∧ ResidentAt child path resident ∧ resident.owner = owner := by
  refine CopyFields.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ fields _ _ origins _ => ∀ owner fresh, (owner,fresh) ∈ origins →
      ∃ (index : Nat) (child : Value) (path : List Nat) (resident : Value),
        fields[index]? = some (some child) ∧ ResidentAt child path resident ∧ resident.owner = owner)
    ?_ ?_ ?_ copy
  · intros; trivial
  · intro next owner fresh member; cases member
  · intro next middle finish value copied rest copies first later tree _ _ ih owner fresh member
    rcases List.mem_append.mp member with earlier | later
    · obtain ⟨path,resident,inside,same⟩ := tree.source_owner owner fresh earlier
      exact ⟨0,value,path,resident,rfl,inside,same⟩
    · obtain ⟨index,child,path,resident,found,inside,same⟩ := ih owner fresh later
      exact ⟨index+1,child,path,resident,found,inside,same⟩

theorem CopyTree.origins_unique {program : Program} {next finish : Nat} {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins)
    (owners : ∀ left right a b, ResidentAt value left a → ResidentAt value right b → a.owner = b.owner → left = right) :
    origins.Unique := by
  refine CopyTree.rec
    (motive_1 := fun _ value _ _ origins _ =>
      (∀ left right a b, ResidentAt value left a → ResidentAt value right b → a.owner = b.owner → left = right) → origins.Unique)
    (motive_2 := fun _ fields _ _ origins _ =>
      (∀ (first second : Nat) left right x y a b, fields[first]? = some (some x) → fields[second]? = some (some y) →
        ResidentAt x left a → ResidentAt y right b → a.owner = b.owner → first = second ∧ left = right) → origins.Unique)
    ?_ ?_ ?_ copy owners
  · intro next owner type head fields resources copied finish origins _ _ tree ih unique
    refine List.nodup_cons.mpr ⟨?_,?_⟩
    · intro member
      obtain ⟨⟨key,fresh⟩,present,same⟩ := List.mem_map.mp member
      change key = owner at same
      subst key
      obtain ⟨index,child,path,resident,found,inside,ownerEq⟩ := tree.source_owner owner fresh present
      have impossible := unique [] (index :: path) _ resident .root (.field found inside) ownerEq.symm
      cases impossible
    · apply ih
      intro first second left right x y a b one two inside nested same
      exact List.cons.inj (unique (first :: left) (second :: right) a b (.field one inside) (.field two nested) same)
  · intro next unique; exact List.nodup_nil
  · intro next middle finish value copied rest copies first later tree tail ih restIH unique
    change ((first ++ later).map Prod.fst).Nodup
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨?_,?_,?_⟩
    · apply ih
      intro left right a b inside nested same
      exact (unique 0 0 left right value value a b rfl rfl inside nested same).2
    · apply restIH
      intro first second left right x y a b one two inside nested same
      obtain ⟨indices,paths⟩ := unique (first+1) (second+1) left right x y a b one two inside nested same
      exact ⟨Nat.add_right_cancel indices,paths⟩
    · intro owner inFirst other inLater same
      subst other
      obtain ⟨⟨key,fresh⟩,member,equal⟩ := List.mem_map.mp inFirst
      change key = owner at equal
      subst key
      obtain ⟨⟨key,last⟩,laterMember,equal⟩ := List.mem_map.mp inLater
      change key = owner at equal
      subst key
      obtain ⟨left,a,inside,leftOwner⟩ := tree.source_owner owner fresh member
      obtain ⟨index,child,right,b,found,nested,rightOwner⟩ := tail.source_owner owner last laterMember
      have impossible := (unique 0 (index+1) left right value child a b rfl found inside nested (leftOwner.trans rightOwner.symm)).1
      cases impossible

theorem CopyValue.exists {program : Kernel.Program} {world : World} {address : Address} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (well : world.WellFormed) (typed : Typing.ValueTyped program world value)
    (resident : world.Resident address value) (initialized : value.Initialized)
    (closed : value.ResourcesClosed program world) (capability : PrincipalOf program.declarations value.type .duplicable)
    (next : Nat) : ∃ finish copied, CopyValue program.declarations next value finish copied := by
  obtain ⟨finish,raw,origins,tree⟩ := CopyTree.exists initialized (typed.copy_residents valid inventory well closed capability) next
  refine ⟨finish,_,.copy tree (tree.origins_unique ?_)⟩
  intro left right a b inside nested same
  have first := (World.resident_iff_stores.mp resident).residentAt inside
  have second := (World.resident_iff_stores.mp resident).residentAt nested
  have addresses := well.2.2.2.2.2.2.2.1 _ _ a b first second same
  exact List.append_cancel_left (congrArg Address.fields addresses)

theorem Copies.exists {program : Kernel.Program} {before : World} {authority : Authority}
    {source destination : Address} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before) (stored : before.Stores source value) (initialized : value.Initialized)
    (ready : value.HandoffReady program before .shared [destination])
    (capability : PrincipalOf program.declarations value.type .duplicable)
    (permission : Permitted before authority .shared source) (vacant : before.Vacant destination)
    (type : AddressType program.declarations before destination value.type) :
    ∃ after, Copies program before authority source destination after ∧ Typing.WorldTyped program after := by
  obtain ⟨next,cloned,copy⟩ := CopyValue.exists valid inventory typed.1 (World.stores_typed typed.roots stored)
    (World.resident_iff_stores.mpr stored) initialized ready.1.1 capability before.nextOwner
  obtain ⟨after,written⟩ := vacant.write_exists (some cloned)
  have copied := Copies.copy stored initialized ready permission vacant type copy written
  exact ⟨_,copied,copied.worldTyped valid inventory typed⟩

theorem Acquires.loans {program : RuntimeProgram} {before after : World}
    {authority : Authority} {force : Bool} {source destination : Address}
    (acquired : Acquires program before authority force source destination after) :
    after.loans = before.loans := by
  cases acquired with
  | explicitMove moved => exact moved.loans
  | move _ _ _ moved => exact moved.loans
  | copy copied =>
      cases copied with
      | copy _ _ _ _ _ _ _ written =>
          have loans := World.write_loans written
          exact loans

theorem Acquires.locations {program : RuntimeProgram} {before after : World}
    {authority : Authority} {force : Bool} {source destination : Address}
    (acquired : Acquires program before authority force source destination after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  cases acquired with
  | explicitMove moved => exact moved.locations id
  | move _ _ _ moved => exact moved.locations id
  | copy copied => exact copied.locations id

theorem Transfers.destination_supportOutside {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {value : Value}
    (moved : Transfers program before authority source destination after)
    (stored : after.Stores destination value) : value.SupportOutside after destination := by
  obtain ⟨original,selected⟩ : ∃ original, before.Stores source original := by
    cases moved with
    | move selected _ _ _ _ _ _ _ _ => exact ⟨_,selected⟩
  have same := Option.some.inj (stored.symm.trans (moved.handed_off_ready selected).1)
  subst value
  have ready := (moved.moveReady selected).frame (.of_locations moved.locations) moved.loans (moved.supportFramed selected)
  exact ready.2 destination (by simp)

theorem Acquires.destination_supportOutside {program : RuntimeProgram} {before after : World}
    {authority : Authority} {force : Bool} {source destination : Address} {value : Value}
    (acquired : Acquires program before authority force source destination after)
    (stored : after.Stores destination value) : value.SupportOutside after destination := by
  cases acquired with
  | explicitMove moved => exact moved.destination_supportOutside stored
  | move _ _ _ moved => exact moved.destination_supportOutside stored
  | copy copied =>
      cases copied with
      | copy selected initialized ready permission vacant located copy written =>
          rename_i original cloned next installed
          have installedValue := World.write_read_inside written []
          simp only [List.append_nil] at installedValue
          have same : value = cloned := Option.some.inj (stored.symm.trans installedValue)
          subst value
          have clonedReady := ready.copy copy
          have framed : cloned.SupportFramed before {installed with nextOwner := next} := by
            intro address supported
            refine ⟨?_,World.write_locations written address.root⟩
            change installed.read address = before.read address
            exact World.write_disjoint written (clonedReady.2 destination (by simp) address supported)
          have loans := World.write_loans written
          have locations := World.write_locations written
          have preserved := clonedReady.frame (after := {installed with nextOwner := next})
            (.of_locations locations) loans framed
          exact preserved.2 destination (by simp)

theorem Acquires.handed_off_ready {program : Kernel.Program} {before after : World}
    {authority : Authority} {force : Bool} {source destination : Address}
    (valid : ProgramWellFormed program.declarations) (typed : Typing.WorldTyped program before)
    (acquired : Acquires program before authority force source destination after) :
    ∃ value, after.Stores destination value ∧ value.Initialized ∧ value.ResourcesAccessible program after .owned := by
  cases acquired with
  | explicitMove moved =>
      cases moved with
      | move stored initialized ready permission vacant separated type clear install =>
          exact ⟨_,(Transfers.move stored initialized ready permission vacant separated type clear install).handed_off_ready stored⟩
  | copy copied => exact copied.handed_off_ready valid typed
  | move stored _ _ moved => exact ⟨_,moved.handed_off_ready stored⟩

/-- The semantic principal, not a syntactic guess about the resident head,
fixes implicit acquisition of a duplicable source to the real Copy branch. -/
theorem Acquires.implicit_copy {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {value : Value}
    (stored : before.Stores source value) (capability : PrincipalOf program.declarations value.type .duplicable)
    (acquired : Acquires program before authority false source destination after) :
    Copies program before authority source destination after := by
  cases acquired with
  | copy copied => exact copied
  | move selected actual noncopy moved =>
      have same := Option.some.inj (stored.symm.trans selected)
      subst_vars
      have principalEq := Option.some.inj ((principalOf_canonical.mp actual).symm.trans (principalOf_canonical.mp capability))
      exact False.elim (noncopy principalEq)

/-- The force flag selects explicit transfer without capability classification;
only implicit acquisition consults the semantic principal. Only the selected
branch's permission/readiness is required. No completed acquisition or storage
write is assumed. -/
theorem Acquires.exists {program : Kernel.Program} {before : World} {authority : Authority}
    {force : Bool} {principal : Principal} {source destination : Address} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before) (stored : before.Stores source value) (initialized : value.Initialized)
    (capability : force = false → PrincipalOf program.declarations value.type principal)
    (copyReady : force = false → principal = .duplicable →
      value.HandoffReady program before .shared [destination] ∧ Permitted before authority .shared source)
    (moveReady : force = true ∨ principal ≠ .duplicable →
      value.MoveReady program before [source,destination] ∧ Permitted before authority .owned source ∧ ¬ source.Overlaps destination)
    (vacant : before.Vacant destination) (type : AddressType program.declarations before destination value.type) :
    ∃ after, Acquires program before authority force source destination after ∧ Typing.WorldTyped program after ∧
      ∃ result, after.Stores destination result ∧ result.Initialized ∧ result.ResourcesAccessible program after .owned := by
  by_cases copying : force = false ∧ principal = .duplicable
  · obtain ⟨rfl,rfl⟩ := copying
    obtain ⟨ready,permission⟩ := copyReady rfl rfl
    obtain ⟨after,copied,afterTyped⟩ := Copies.exists valid inventory typed stored initialized ready (capability rfl) permission vacant type
    exact ⟨after,.copy copied,afterTyped,copied.handed_off_ready valid typed⟩
  · have moving : force = true ∨ principal ≠ .duplicable := by
      cases force with
      | true => exact Or.inl rfl
      | false => exact Or.inr (fun same => copying ⟨rfl,same⟩)
    obtain ⟨ready,permission,separated⟩ := moveReady moving
    obtain ⟨after,moved⟩ := Transfers.exists stored initialized ready permission vacant separated type
    have acquired : Acquires program before authority force source destination after := by
      cases force with
      | true => exact .explicitMove moved
      | false => exact .move stored (capability rfl) (fun same => copying ⟨rfl,same⟩) moved
    exact ⟨after,acquired,moved.worldTyped valid inventory typed,⟨value,moved.handed_off_ready stored⟩⟩

/-- Copy itself does not consume a physical allocation. When the destination
must first be allocated, this theorem uses the SAME positive request and
physical-exhaustion alternative as every ordinary allocation producer. -/
theorem Acquires.allocate_success_or_exhausted {program : Kernel.Program} {before : World} {authority : Authority}
    {force : Bool} {principal : Principal} {source : Address} {value : Value}
    {home : Home} {region : Identity} {layout : Layout} {mutable : Bool}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before) (stored : before.Stores source value) (initialized : value.Initialized)
    (capability : force = false → PrincipalOf program.declarations value.type principal)
    (copyReady : force = false → principal = .duplicable →
      value.ResourcesAccessible program before .shared ∧ Permitted before authority .shared source)
    (moveReady : force = true ∨ principal ≠ .duplicable →
      value.MoveReady program before [source] ∧ Permitted before authority .owned source)
    (request : AllocationRequest program.declarations before region value.type layout) :
    (∃ destination allocated after, Allocates program.declarations before home region value.type layout mutable destination allocated ∧
      Acquires program allocated authority force source destination after ∧ Typing.WorldTyped program after ∧
      ∃ result, after.Stores destination result ∧ result.Initialized ∧ result.ResourcesAccessible program after .owned) ∨
      AllocationExhausted program.declarations before region value.type layout := by
  rcases request.success_or_exhausted home mutable with ⟨destination,allocated,allocation⟩ | exhausted
  · have fresh : destination.root = before.nextRoot := by cases allocation; rfl
    have afterStored : allocated.Stores source value := (allocation.read typed.1 source).trans stored
    have copiedReady : force = false → principal = .duplicable →
        value.HandoffReady program allocated .shared [destination] ∧ Permitted allocated authority .shared source := by
      intro forced principalEq
      obtain ⟨ready,permission⟩ := copyReady forced principalEq
      have sourceReady : value.HandoffReady program before .shared [destination] := by
        refine ⟨ready,?_⟩
        intro address member
        have same := List.mem_singleton.mp member
        subst address
        exact ready.supportOutside_fresh typed.1 (Nat.le_of_eq fresh.symm)
      exact ⟨allocation.handoffReady typed.1 sourceReady,
        permission.locationExtension (allocation.locationExtension typed.1) allocation.loans⟩
    have movedReady : force = true ∨ principal ≠ .duplicable →
        value.MoveReady program allocated [source,destination] ∧ Permitted allocated authority .owned source ∧ ¬ source.Overlaps destination := by
      intro moving
      obtain ⟨ready,permission⟩ := moveReady moving
      have sourceReady : value.MoveReady program before [source,destination] := by
        refine ⟨ready.1,?_⟩
        intro address member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact ready.2 _ List.mem_cons_self
        · exact ready.1.supportOutside_fresh typed.1 (Nat.le_of_eq fresh.symm)
      refine ⟨allocation.handoffReady typed.1 sourceReady,
        permission.locationExtension (allocation.locationExtension typed.1) allocation.loans,?_⟩
      intro overlap
      obtain ⟨root,selected⟩ := permission.root
      have bound := World.root_bound typed.1 (World.root_found selected).1
      exact Nat.lt_irrefl _ ((overlap.1.trans fresh) ▸ bound)
    obtain ⟨after,acquired,afterTyped,result⟩ := Acquires.exists valid inventory (allocation.worldTyped typed) afterStored initialized capability
      copiedReady movedReady allocation.created_vacant allocation.created_addressType
    exact Or.inl ⟨destination,allocated,after,allocation,acquired,afterTyped,result⟩
  · exact Or.inr exhausted

theorem Copies.allocate_success_or_exhausted {program : Kernel.Program} {before : World} {authority : Authority}
    {source : Address} {value : Value} {home : Home} {region : Identity} {layout : Layout} {mutable : Bool}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before) (stored : before.Stores source value) (initialized : value.Initialized)
    (ready : value.ResourcesAccessible program before .shared)
    (capability : PrincipalOf program.declarations value.type .duplicable)
    (permission : Permitted before authority .shared source)
    (request : AllocationRequest program.declarations before region value.type layout) :
    (∃ destination allocated after, Allocates program.declarations before home region value.type layout mutable destination allocated ∧
      Copies program allocated authority source destination after ∧ Typing.WorldTyped program after ∧
      ∃ result, after.Stores destination result ∧ result.Initialized ∧ result.ResourcesAccessible program after .owned) ∨
      AllocationExhausted program.declarations before region value.type layout := by
  have movement : false = true ∨ Principal.duplicable ≠ .duplicable →
      value.MoveReady program before [source] ∧ Permitted before authority .owned source := by
    rintro (impossible | impossible)
    · cases impossible
    · exact False.elim (impossible rfl)
  rcases Acquires.allocate_success_or_exhausted (home := home) (mutable := mutable) valid inventory typed stored initialized (fun _ => capability)
      (fun _ _ => ⟨ready,permission⟩) movement request with ⟨destination,allocated,after,allocation,acquired,afterTyped,result⟩ | exhausted
  · exact Or.inl ⟨destination,allocated,after,allocation,
      acquired.implicit_copy ((allocation.read typed.1 source).trans stored) capability,afterTyped,result⟩
  · exact Or.inr exhausted

theorem Copies.source_present {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address}
    (copied : Copies program before authority source destination after) : (after.read source).isSome = true := by
  cases copied with
  | copy stored _ _ _ vacant _ _ written =>
      have separated : ¬ destination.Prefix source := fun included => vacant.not_stored (stored.prefix included)
      have framed := World.write_read_shell written separated
      rw [stored] at framed
      obtain ⟨value,found,_⟩ := Option.map_eq_some_iff.mp framed
      exact Option.isSome_iff_exists.mpr ⟨value,found⟩

namespace Execution

open Kernel

theorem AtomStep.copy_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination source : Address} {place : Place} {next : Code} {authority : Authority} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .atom context destination (.acquire place false) next)
    (resolved : ResolvesPlace before.world context.environment place source authority)
    (stored : before.world.Stores source value) (initialized : value.Initialized)
    (ready : value.HandoffReady program before.world .shared [destination])
    (capability : PrincipalOf program.declarations value.type .duplicable)
    (permission : Permitted before.world authority .shared source) (vacant : before.world.Vacant destination)
    (type : AddressType program.declarations before.world destination value.type) :
    ∃ after, AtomStep program before (some (.copy source destination)) after ∧ Typing.WorldTyped program after.world ∧
      ∃ result, after.world.Stores destination result ∧ result.Initialized ∧ result.ResourcesAccessible program after.world .owned := by
  obtain ⟨after,copied,afterTyped⟩ := Copies.exists valid inventory typed stored initialized ready capability permission vacant type
  refine ⟨{before with world := after, task := .run context next},?_,afterTyped,copied.handed_off_ready valid typed⟩
  have step := AtomStep.acquire task resolved (Acquires.copy copied)
  simpa only [Bool.false_eq_true,if_false,copied.source_present,if_true] using step

theorem AtomStep.acquire_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination source : Address} {place : Place} {next : Code} {authority : Authority}
    {force : Bool} {principal : Principal} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .atom context destination (.acquire place force) next)
    (resolved : ResolvesPlace before.world context.environment place source authority)
    (stored : before.world.Stores source value) (initialized : value.Initialized)
    (capability : force = false → PrincipalOf program.declarations value.type principal)
    (copyReady : force = false → principal = .duplicable →
      value.HandoffReady program before.world .shared [destination] ∧ Permitted before.world authority .shared source)
    (moveReady : force = true ∨ principal ≠ .duplicable →
      value.MoveReady program before.world [source,destination] ∧ Permitted before.world authority .owned source ∧ ¬ source.Overlaps destination)
    (vacant : before.world.Vacant destination) (type : AddressType program.declarations before.world destination value.type) :
    ∃ event after, AtomStep program before event after ∧ Typing.WorldTyped program after.world ∧
      ∃ result, after.world.Stores destination result ∧ result.Initialized ∧ result.ResourcesAccessible program after.world .owned := by
  obtain ⟨after,acquired,afterTyped,result⟩ := Acquires.exists valid inventory typed stored initialized capability copyReady moveReady vacant type
  exact ⟨_,_,.acquire task resolved acquired,afterTyped,result⟩

theorem Step.copy_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination source : Address} {place : Place} {next : Code} {authority : Authority} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .atom context destination (.acquire place false) next)
    (resolved : ResolvesPlace before.world context.environment place source authority)
    (stored : before.world.Stores source value) (initialized : value.Initialized)
    (ready : value.HandoffReady program before.world .shared [destination])
    (capability : PrincipalOf program.declarations value.type .duplicable)
    (permission : Permitted before.world authority .shared source) (vacant : before.world.Vacant destination)
    (type : AddressType program.declarations before.world destination value.type) :
    ∃ after, Step program host before (some (.copy source destination)) after ∧ Typing.WorldTyped program after.world ∧
      ∃ result, after.world.Stores destination result ∧ result.Initialized ∧ result.ResourcesAccessible program after.world .owned := by
  obtain ⟨after,step,afterTyped,result⟩ := AtomStep.copy_progress valid inventory typed task resolved stored initialized ready capability permission vacant type
  exact ⟨after,Or.inr (Or.inl step),afterTyped,result⟩

theorem Step.acquire_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination source : Address} {place : Place} {next : Code} {authority : Authority}
    {force : Bool} {principal : Principal} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .atom context destination (.acquire place force) next)
    (resolved : ResolvesPlace before.world context.environment place source authority)
    (stored : before.world.Stores source value) (initialized : value.Initialized)
    (capability : force = false → PrincipalOf program.declarations value.type principal)
    (copyReady : force = false → principal = .duplicable →
      value.HandoffReady program before.world .shared [destination] ∧ Permitted before.world authority .shared source)
    (moveReady : force = true ∨ principal ≠ .duplicable →
      value.MoveReady program before.world [source,destination] ∧ Permitted before.world authority .owned source ∧ ¬ source.Overlaps destination)
    (vacant : before.world.Vacant destination) (type : AddressType program.declarations before.world destination value.type) :
    ∃ event after, Step program host before event after ∧ Typing.WorldTyped program after.world ∧
      ∃ result, after.world.Stores destination result ∧ result.Initialized ∧ result.ResourcesAccessible program after.world .owned := by
  obtain ⟨event,after,step,afterTyped,result⟩ := AtomStep.acquire_progress valid inventory typed task resolved stored initialized capability copyReady moveReady vacant type
  exact ⟨event,after,Or.inr (Or.inl step),afterTyped,result⟩

end Execution

end Glorious.Language
