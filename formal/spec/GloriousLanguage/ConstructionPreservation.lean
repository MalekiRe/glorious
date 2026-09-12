import GloriousLanguage.CopyPreservation

/-! Preservation for moving evaluated inputs into newly constructed values.
The same source addresses and acquired residents are used for clear, install,
ownership identity and typing; no later source lookup reconstructs an input. -/
namespace Glorious.Language

theorem Permitted.transport {before after : World} {authority : Authority} {access : Access} {address : Address}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (loans : after.loans = before.loans) (permission : Permitted before authority access address) :
    Permitted after authority access address := by
  induction authority with
  | owner =>
      obtain ⟨⟨root,selected⟩,allowed⟩ := permission
      obtain ⟨changed,found,_⟩ := World.root_transport locations selected
      exact ⟨⟨changed,found⟩,by simpa only [loans] using allowed⟩
  | loan id =>
      obtain ⟨⟨root,selected⟩,active,found,live,rootEq,generation,path,mode,allowed⟩ := permission
      obtain ⟨changed,selected,_⟩ := World.root_transport locations selected
      refine ⟨⟨changed,selected⟩,active,by simpa only [loans] using found,live,rootEq,generation,path,mode,?_⟩
      intro other loan found live different overlap conflict
      have oldFound : before.loans.get other = some loan := by simpa only [loans] using found
      exact AncestorLoan.transport loans (allowed other loan oldFound live different overlap conflict)
  | shared backing ih =>
      obtain ⟨root,selected⟩ := permission.1
      obtain ⟨changed,found,_⟩ := World.root_transport locations selected
      exact ⟨⟨changed,found⟩,permission.2.1,ih permission.2.2⟩

theorem Clears.locations {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  induction cleared with
  | nil => rfl
  | cons written _ ih => exact ih.trans (World.write_locations written id)

theorem Clears.rest {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) : after = { before with roots := after.roots } := by
  induction cleared with
  | nil => rfl
  | cons written _ ih =>
      have first := World.write_rest written
      conv => lhs; rw [ih,first]

theorem Clears.loans {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) : after.loans = before.loans := by
  have rest := cleared.rest
  have same := congrArg World.loans rest
  exact same

theorem Clears.permitted {before after : World} {addresses : List Address}
    {authority : Authority} {access : Access} {address : Address} (cleared : Clears before addresses after)
    (permission : Permitted before authority access address) : Permitted after authority access address :=
  permission.transport cleared.locations cleared.loans

theorem Clears.wellFormedWithOrigins {before after : World} {addresses : List Address} {originBound : Identity}
    (valid : before.WellFormedWithOrigins originBound)
    (allowed : ∀ address ∈ addresses, ∃ authority, Permitted before authority .owned address)
    (cleared : Clears before addresses after) : after.WellFormedWithOrigins originBound := by
  induction cleared with
  | nil => exact valid
  | cons written rest ih =>
      obtain ⟨authority,permission⟩ := allowed _ List.mem_cons_self
      apply ih (World.clear_wellFormedWithOrigins valid permission written)
      intro address member
      obtain ⟨authority,permission⟩ := allowed address (List.mem_cons_of_mem _ member)
      exact ⟨authority,permission.transport (World.write_locations written) (World.write_loans written)⟩

theorem Clears.wellFormed {before after : World} {addresses : List Address}
    (valid : before.WellFormed)
    (allowed : ∀ address ∈ addresses, ∃ authority, Permitted before authority .owned address)
    (cleared : Clears before addresses after) : after.WellFormed := by
  have checked := cleared.wellFormedWithOrigins valid allowed
  simpa only [World.WellFormed,congrArg World.nextOwner cleared.rest] using checked

theorem Clears.worldTyped {program : Kernel.Program} {before after : World} {addresses : List Address}
    (typed : Typing.WorldTyped program before)
    (allowed : ∀ address ∈ addresses, ∃ authority, Permitted before authority .owned address)
    (cleared : Clears before addresses after) : Typing.WorldTyped program after := by
  induction cleared with
  | nil => exact typed
  | cons written rest ih =>
      obtain ⟨authority,permission⟩ := allowed _ List.mem_cons_self
      apply ih (World.clear_worldTyped typed permission written)
      intro address member
      obtain ⟨authority,permission⟩ := allowed address (List.mem_cons_of_mem _ member)
      exact ⟨authority,permission.transport (World.write_locations written) (World.write_loans written)⟩

theorem Clears.resident_origin {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) {address : Address} {value : Value} (resident : after.Resident address value) :
    ∃ original, before.Resident address original ∧ value.shell = original.shell := by
  induction cleared with
  | nil => exact ⟨value,resident,rfl⟩
  | cons written _ ih =>
      obtain ⟨middle,oldResident,last⟩ := ih resident
      obtain ⟨original,found,first⟩ := World.clear_resident_origin written oldResident
      exact ⟨original,found,last.trans first⟩

theorem World.clear_absent {before after : World} {mutation address : Address}
    (written : before.write mutation none = some after) (absent : before.read address = none) : after.read address = none := by
  by_cases included : mutation.Prefix address
  · obtain ⟨suffix,equal⟩ := Address.prefix_extension included
    have empty := World.write_read_inside written suffix
    change after.read { mutation with fields := mutation.fields ++ suffix } = none at empty
    simpa only [← equal] using empty
  · have shell := World.write_read_shell written included
    rw [absent] at shell
    exact Option.map_eq_none_iff.mp shell

theorem Clears.absent {before after : World} {addresses : List Address} {address : Address}
    (cleared : Clears before addresses after) (absent : before.read address = none) : after.read address = none := by
  induction cleared with
  | nil => exact absent
  | cons written _ ih => exact ih (World.clear_absent written absent)

theorem Clears.cleared {before after : World} {addresses : List Address} {address : Address}
    (cleared : Clears before addresses after) (member : address ∈ addresses) (suffix : List Nat) :
    after.read { address with fields := address.fields ++ suffix } = none := by
  induction cleared with
  | nil => simp at member
  | cons written rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact rest.absent (World.write_read_inside written suffix)
      · exact ih later

theorem World.Vacant.read_none {world : World} {address : Address} (vacant : world.Vacant address) :
    world.read address = none := by
  cases found : world.read address with
  | none => rfl
  | some value => exact False.elim (vacant.not_stored ⟨value,found⟩)

theorem World.Vacant.clear {before after : World} {mutation address : Address}
    (vacant : before.Vacant address) (written : before.write mutation none = some after)
    (outside : ¬ mutation.ProperPrefix address) : after.Vacant address := by
  rcases World.write_located written outside (Or.inr vacant) with ⟨value,stored⟩ | vacant
  · have absent := World.clear_absent written vacant.read_none
    rw [stored] at absent
    cases absent
  · exact vacant

theorem Clears.vacant {before after : World} {addresses : List Address} {destination : Address}
    (cleared : Clears before addresses after) (vacant : before.Vacant destination)
    (outside : ∀ source ∈ addresses, ¬ source.ProperPrefix destination) : after.Vacant destination := by
  induction cleared with
  | nil => exact vacant
  | cons written _ ih =>
      exact ih (vacant.clear written (outside _ (by simp))) (fun source member => outside source (List.mem_cons_of_mem _ member))

theorem Clears.address_type {program : Program} {before after : World} {addresses : List Address}
    {destination : Address} {type : Term} (cleared : Clears before addresses after)
    (located : AddressType program before destination type)
    (outside : ∀ source ∈ addresses, ¬ source.ProperPrefix destination) : AddressType program after destination type := by
  induction cleared with
  | nil => exact located
  | cons written _ ih =>
      exact ih ((World.write_address_types written (outside _ (by simp))).mp located)
        (fun source member => outside source (List.mem_cons_of_mem _ member))

theorem ListRel.get_right {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right) {index : Nat} {value : β} (found : right[index]? = some value) :
    ∃ original, left[index]? = some original ∧ relation original value := by
  induction related generalizing index with
  | nil => simp at found
  | cons relation rest ih =>
      cases index with
      | zero =>
          cases Option.some.inj found
          exact ⟨_,rfl,relation⟩
      | succ index => exact ih found

theorem Address.Prefix.overlap_of_common {left right common : Address}
    (first : left.Prefix common) (second : right.Prefix common) : left.Overlaps right := by
  refine ⟨first.1.trans second.1.symm,first.2.1.trans second.2.1.symm,?_⟩
  have a := List.prefix_iff_exists_eq_append.mpr first.2.2
  have b := List.prefix_iff_exists_eq_append.mpr second.2.2
  rcases List.prefix_or_prefix_of_prefix a b with included | included
  · exact Or.inr (List.prefix_iff_exists_eq_append.mp included)
  · exact Or.inl (List.prefix_iff_exists_eq_append.mp included)

theorem _root_.List.Pairwise.get_other {α : Type} {relation : α → α → Prop} {values : List α}
    (paired : values.Pairwise relation) (symmetric : ∀ {a b}, relation a b → relation b a)
    {first second : Nat} {left right : α} (a : values[first]? = some left) (b : values[second]? = some right)
    (different : first ≠ second) : relation left right := by
  obtain ⟨firstBound,firstEq⟩ := List.getElem?_eq_some_iff.mp a
  obtain ⟨secondBound,secondEq⟩ := List.getElem?_eq_some_iff.mp b
  rcases Nat.lt_or_gt_of_ne different with less | greater
  · simpa [firstEq,secondEq] using (List.pairwise_iff_getElem.mp paired first second firstBound secondBound less)
  · exact symmetric (by simpa [firstEq,secondEq] using
      (List.pairwise_iff_getElem.mp paired second first secondBound firstBound greater))

theorem Value.constructed_origin {world : World} {owner : Identity} {type : Term} {head : ValueHead}
    {sources : List ResolvedPlace} {values : List Value} {path : List Nat} {value : Value}
    (inputs : ListRel (fun source value => world.Stores source.address value) sources values)
    (inside : ResidentAt (.resident owner type head true (values.map some)) path value) :
    (path = [] ∧ value = .resident owner type head true (values.map some)) ∨
    ∃ index suffix source original, path = index :: suffix ∧ sources[index]? = some source ∧
      world.Stores source.address original ∧ ResidentAt original suffix value := by
  cases inside with
  | root => exact Or.inl ⟨rfl,rfl⟩
  | @field _ index child path _ selected nested =>
      have found : values[index]? = some child := by
        change (values.map some)[index]? = some (some child) at selected
        rw [List.getElem?_map] at selected
        cases atValue : values[index]? <;> simp_all
      obtain ⟨source,atSource,stored⟩ := inputs.get_right found
      exact Or.inr ⟨index,path,source,child,rfl,atSource,stored,nested⟩

theorem Value.constructed_owner_bound {world : World} {type : Term} {head : ValueHead}
    {sources : List ResolvedPlace} {values : List Value} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound)
    (inputs : ListRel (fun source value => world.Stores source.address value) sources values)
    {path : List Nat} {value : Value} (inside : ResidentAt (.resident world.nextOwner type head true (values.map some)) path value) :
    value.owner < world.nextOwner+1 := by
  rcases Value.constructed_origin inputs inside with ⟨_,rfl⟩ | ⟨_,_,_,_,_,_,stored,nested⟩
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_lt (World.owner_bound valid (stored.residentAt nested))

theorem Value.constructed_owner_unique {world : World} {type : Term} {head : ValueHead}
    {sources : List ResolvedPlace} {values : List Value} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound)
    (inputs : ListRel (fun source value => world.Stores source.address value) sources values)
    (separate : sources.Pairwise (fun left right => ¬ left.address.Overlaps right.address)) :
    ∀ left right x y, ResidentAt (.resident world.nextOwner type head true (values.map some)) left x →
      ResidentAt (.resident world.nextOwner type head true (values.map some)) right y → x.owner = y.owner → left = right := by
  intro left right x y first second same
  rcases Value.constructed_origin inputs first with ⟨rfl,rfl⟩ | ⟨leftIndex,leftPath,leftSource,leftValue,rfl,leftFound,leftStored,leftInside⟩
  · rcases Value.constructed_origin inputs second with ⟨rfl,rfl⟩ | ⟨index,path,source,value,rfl,found,stored,inside⟩
    · rfl
    · have bound := World.owner_bound valid (stored.residentAt inside)
      change world.nextOwner = y.owner at same
      rw [← same] at bound
      exact False.elim (Nat.lt_irrefl _ bound)
  · rcases Value.constructed_origin inputs second with ⟨rfl,rfl⟩ | ⟨rightIndex,rightPath,rightSource,rightValue,rfl,rightFound,rightStored,rightInside⟩
    · have bound := World.owner_bound valid (leftStored.residentAt leftInside)
      change x.owner = world.nextOwner at same
      rw [same] at bound
      exact False.elim (Nat.lt_irrefl _ bound)
    · have equal := valid.2.2.2.2.2.2.2.1 _ _ x y (leftStored.residentAt leftInside) (rightStored.residentAt rightInside) same
      by_cases indexSame : leftIndex = rightIndex
      · subst rightIndex
        have sourceSame := Option.some.inj (leftFound.symm.trans rightFound)
        subst rightSource
        have pathSame := List.append_cancel_left (congrArg Address.fields equal)
        simp [pathSame]
      · have disjoint := separate.get_other (fun different overlap => different overlap.symm) leftFound rightFound indexSame
        apply False.elim
        apply disjoint
        apply Address.Prefix.overlap_of_common (common := { leftSource.address with fields := leftSource.address.fields ++ leftPath })
        · exact ⟨rfl,rfl,leftPath,rfl⟩
        · rw [equal]
          exact ⟨rfl,rfl,rightPath,rfl⟩

theorem NewValue.locations {program : Program} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  cases constructed with
  | construct _ _ _ _ _ _ cleared written => exact (World.write_locations written id).trans (cleared.locations id)

theorem NewValue.wellFormedWithOrigins {program : Program} {before after : World} {destination type head sources}
    {originBound : Identity} (valid : before.WellFormedWithOrigins originBound)
    (headReferences : ∀ id, head = .reference id → ∃ loan, before.loans.get id = some loan ∧ loan.live = true)
    (headPacks : ∀ pack, head = .bindings pack →
      pack.brand < before.nextProof ∧ pack.region ∈ before.liveRegions ∧ pack.fields.length = sources.length ∧
      pack.fields.Nodup ∧ ∀ fact ∈ pack.facts, fact.resultOrigin < originBound)
    (constructed : NewValue program before destination type head sources after) : after.WellFormedWithOrigins originBound := by
  cases constructed with
  | construct vacant destinationType inputs initialized separate permissions cleared written =>
    have allowed : ∀ address ∈ sources.map ResolvedPlace.address, ∃ authority, Permitted before authority .owned address := by
      intro address member
      obtain ⟨source,sourceMember,rfl⟩ := List.mem_map.mp member
      exact ⟨source.authority,(permissions source sourceMember).1⟩
    have outside : ∀ source ∈ sources.map ResolvedPlace.address, ¬ source.ProperPrefix destination := by
      intro address member included
      obtain ⟨source,sourceMember,rfl⟩ := List.mem_map.mp member
      exact (permissions source sourceMember).2 included.1.overlaps
    have rest := cleared.rest
    have ownerEq := congrArg World.nextOwner rest
    have proofEq := congrArg World.nextProof rest
    have regionsEq := congrArg World.liveRegions rest
    apply World.install_wellFormedWithOrigins (cleared.wellFormedWithOrigins valid allowed) (cleared.vacant vacant outside)
      (by simpa only [ownerEq] using Nat.le_succ before.nextOwner)
      (fun _ _ inside => Value.constructed_owner_bound valid inputs inside)
      (Value.constructed_owner_unique valid inputs separate) ?_ ?_ ?_ written
    · intro path value inside address original resident same
      obtain ⟨oldOriginal,oldResident,shell⟩ := cleared.resident_origin resident
      have oldOwner : original.owner = oldOriginal.owner := by
        simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shell
      rcases Value.constructed_origin inputs inside with ⟨_,rfl⟩ | ⟨index,suffix,source,sourceValue,_,found,stored,nested⟩
      · have bound := World.owner_bound valid oldResident
        change before.nextOwner = original.owner at same
        rw [← oldOwner,← same] at bound
        exact Nat.lt_irrefl _ bound
      · have identity := valid.2.2.2.2.2.2.2.1 _ _ value oldOriginal
          (stored.residentAt nested) oldResident (same.trans oldOwner)
        have member : source.address ∈ sources.map ResolvedPlace.address :=
          List.mem_map.mpr ⟨source,List.mem_of_getElem? found,rfl⟩
        have absent := cleared.cleared member suffix
        rw [identity,World.resident_iff_stores.mp resident] at absent
        cases absent
    · intro path value pack inside headEq
      rcases Value.constructed_origin inputs inside with ⟨_,rfl⟩ | ⟨_,_,_,_,_,_,stored,nested⟩
      · obtain ⟨brand,region,length,distinct,facts⟩ := headPacks pack headEq
        refine ⟨by simpa only [proofEq] using brand,by simpa only [regionsEq] using region,?_,distinct,facts⟩
        simpa only [Value.fields,List.length_map] using length.trans inputs.length_eq
      · obtain ⟨brand,region,length,distinct,facts⟩ := valid.2.2.2.2.2.1 _ value pack (stored.residentAt nested) headEq
        exact ⟨by simpa only [proofEq] using brand,by simpa only [regionsEq] using region,length,distinct,
          facts⟩
    · intro path value id inside headEq
      have live : ∃ loan, before.loans.get id = some loan ∧ loan.live = true := by
        rcases Value.constructed_origin inputs inside with ⟨_,rfl⟩ | ⟨_,_,_,_,_,_,stored,nested⟩
        · exact headReferences id headEq
        · exact valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ value id (stored.residentAt nested) headEq
      simpa only [cleared.loans] using live

theorem NewValue.rest {program : Program} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after) :
    after = { before with roots := after.roots, nextOwner := before.nextOwner+1 } := by
  cases constructed with
  | construct _ _ _ _ _ _ cleared written =>
      have first := cleared.rest
      have last := World.write_rest written
      conv => lhs; rw [last,first]

theorem NewValue.wellFormed {program : Program} {before after : World} {destination type head sources}
    (valid : before.WellFormed)
    (headReferences : ∀ id, head = .reference id → ∃ loan, before.loans.get id = some loan ∧ loan.live = true)
    (headPacks : ∀ pack, head = .bindings pack →
      pack.brand < before.nextProof ∧ pack.region ∈ before.liveRegions ∧ pack.fields.length = sources.length ∧
      pack.fields.Nodup ∧ ∀ fact ∈ pack.facts, fact.resultOrigin < before.nextOwner+1)
    (constructed : NewValue program before destination type head sources after) : after.WellFormed := by
  have checked := constructed.wellFormedWithOrigins (valid.mono (Nat.le_succ _)) headReferences headPacks
  simpa only [World.WellFormed,congrArg World.nextOwner constructed.rest] using checked

theorem Typing.ValueTyped.construct {program : Kernel.Program} {before after : World}
    {destination type head sources value} {originBound : Identity}
    (valid : before.WellFormedWithOrigins originBound)
    (constructed : NewValue program.declarations before destination type head sources after)
    (typed : Typing.ValueTyped program before value) : Typing.ValueTyped program after value := by
  apply typed.transport ?_ ?_ (fun _ origin => origin.transport constructed.locations)
  · intro id loan found active
    refine ⟨?_,?_⟩
    · have same := congrArg World.loans constructed.rest
      simpa only [same] using found
    · intro type located
      cases constructed with
      | construct vacant _ _ _ _ permissions cleared written =>
        have outside : ∀ address ∈ sources.map ResolvedPlace.address, ¬ address.ProperPrefix loan.referent := by
          intro address member
          obtain ⟨source,inSource,rfl⟩ := List.mem_map.mp member
          exact (permissions source inSource).1.owned_no_loan_descendant (World.loanParents valid) found active
        exact ((World.write_address_types written
          (vacant.no_located_descendant (World.liveLoanLocations valid _ _ found active))).mp
            (cleared.address_type located outside)).retained (fun _ selected => selected) (fun _ => rfl)
  · have same := congrArg World.availability constructed.rest
    exact same

theorem Clears.typed_roots {program : Kernel.Program} {before after typingWorld : World} {addresses : List Address}
    (roots : ∀ id root value, before.roots.get id = some root → root.live = true → root.value = some value →
      Typing.ValueTyped program typingWorld value ∧ value.type = root.type)
    (cleared : Clears before addresses after) :
    ∀ id root value, after.roots.get id = some root → root.live = true → root.value = some value →
      Typing.ValueTyped program typingWorld value ∧ value.type = root.type := by
  induction cleared with
  | nil => exact roots
  | cons written _ ih => exact ih (World.clear_typed_roots roots written)

theorem Clears.dead_root {before after : World} {addresses : List Address} {id : Identity} {root : Root}
    (cleared : Clears before addresses after) (found : after.roots.get id = some root) (dead : root.live ≠ true) :
    before.roots.get id = some root := by
  induction cleared with
  | nil => exact found
  | cons written _ ih => exact World.write_dead_root written (ih found) dead

/-- The head proof concerns the already evaluated input tree in the input
world. Actual construction consumers supply it from ConstructorHead, checked
callable instances or another specific value producer, never post-state typing. -/
theorem NewValue.worldTypedWithOrigins {program : Kernel.Program} {before after : World} {destination type head sources}
    {originBound : Identity}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTypedWithOrigins program before originBound)
    (headReferences : ∀ id, head = .reference id → ∃ loan, before.loans.get id = some loan ∧ loan.live = true)
    (headPacks : ∀ pack, head = .bindings pack →
      pack.brand < before.nextProof ∧ pack.region ∈ before.liveRegions ∧ pack.fields.length = sources.length ∧
      pack.fields.Nodup ∧ ∀ fact ∈ pack.facts, fact.resultOrigin < originBound)
    (headTyped : ∀ values, ListRel (fun source value => before.Stores source.address value) sources values →
      Typing.ValueTyped program before (.resident before.nextOwner type head true (values.map some)))
    (constructed : NewValue program.declarations before destination type head sources after) :
    Typing.WorldTypedWithOrigins program after originBound := by
  have well := constructed.wellFormedWithOrigins typed.1 headReferences headPacks
  have retained : ∀ value, Typing.ValueTyped program before value → Typing.ValueTyped program after value :=
    fun _ value => value.construct typed.1 constructed
  have support : ∀ id root, after.roots.get id = some root → root.type.RuntimeRegionsBelow after.nextRegion := by
    apply World.root_regions_transport typed.2.2.2 constructed.locations
    have same := congrArg World.nextRegion constructed.rest
    exact Nat.le_of_eq same.symm
  cases constructed with
  | construct _ destinationType inputs _ _ permissions cleared written =>
    obtain ⟨offset,destinationType⟩ := destinationType
    have outside : ∀ address ∈ sources.map ResolvedPlace.address, ¬ address.ProperPrefix destination := by
      intro address member included
      obtain ⟨source,inSource,rfl⟩ := List.mem_map.mp member
      exact (permissions source inSource).2 included.1.overlaps
    obtain ⟨offset,located⟩ := cleared.address_type ⟨offset,destinationType⟩ outside
    have roots := World.write_typed_roots valid inventory (cleared.typed_roots typed.roots) located written
      (fun value same => by cases Option.some.inj same; exact ⟨headTyped _ inputs,rfl⟩)
    refine ⟨well,?_,?_,support⟩
    · intro address value resident
      exact retained _ (World.stores_typed roots (World.resident_iff_stores.mp resident))
    · intro id root value found contents
      by_cases live : root.live = true
      · exact (roots id root value found live contents).2
      · exact typed.2.2.1 id root value (cleared.dead_root (World.write_dead_root written found live) live) contents

theorem NewValue.worldTyped {program : Kernel.Program} {before after : World} {destination type head sources}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (headReferences : ∀ id, head = .reference id → ∃ loan, before.loans.get id = some loan ∧ loan.live = true)
    (headPacks : ∀ pack, head = .bindings pack →
      pack.brand < before.nextProof ∧ pack.region ∈ before.liveRegions ∧ pack.fields.length = sources.length ∧
      pack.fields.Nodup ∧ ∀ fact ∈ pack.facts, fact.resultOrigin < before.nextOwner+1)
    (headTyped : ∀ values, ListRel (fun source value => before.Stores source.address value) sources values →
      Typing.ValueTyped program before (.resident before.nextOwner type head true (values.map some)))
    (constructed : NewValue program.declarations before destination type head sources after) : Typing.WorldTyped program after := by
  have checked := constructed.worldTypedWithOrigins valid inventory (typed.mono (Nat.le_succ _)) headReferences headPacks headTyped
  simpa only [Typing.WorldTyped,congrArg World.nextOwner constructed.rest] using checked

theorem Typing.FieldsTyped.present {program : Kernel.Program} {world : World} {values : List Value}
    (typed : ∀ value ∈ values, Typing.ValueTyped program world value) :
    Typing.FieldsTyped program world (values.map some) (values.map Value.type) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .resident (typed value List.mem_cons_self) rfl
        (ih (fun child member => typed child (List.mem_cons_of_mem _ member)))

theorem NewValue.aggregate_worldTyped {program : Kernel.Program} {before after : World}
    {destination type head sources values variant}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (inputs : ListRel (fun source value => before.Stores source.address value) sources values)
    (headType : Execution.ConstructorHead program.declarations type variant (values.map Value.type) head)
    (constructed : NewValue program.declarations before destination type head sources after) : Typing.WorldTyped program after := by
  apply constructed.worldTyped valid inventory typed ?_ ?_ ?_
  · intro id impossible
    rcases headType with ⟨_,_,head⟩ | ⟨_,_,_,_,_,_,head,_⟩ | ⟨_,_,_,_,_,_,_,head,_⟩ <;>
      cases head.symm.trans impossible
  · intro pack impossible
    rcases headType with ⟨_,_,head⟩ | ⟨_,_,_,_,_,_,head,_⟩ | ⟨_,_,_,_,_,_,_,head,_⟩ <;>
      cases head.symm.trans impossible
  · intro current stored
    have same := inputs.functional (fun _ _ _ first second => Option.some.inj (first.symm.trans second)) stored
    subst current
    apply Typing.ValueTyped.aggregate ?_ (Typing.FieldsTyped.present ?_)
    · rcases headType with ⟨type,variant,rfl⟩ | ⟨element,sign,width,length,type,variant,rfl,rest⟩ |
        ⟨id,args,data,constructor,substitution,type,variant,rfl,rest⟩
      · exact Or.inl ⟨type,rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨element,sign,width,length,type,rfl,rfl,rest⟩)
      · exact Or.inr (Or.inr ⟨id,args,data,constructor,substitution,type,rfl,rfl,rest⟩)
    · intro value member
      obtain ⟨index,bound,found⟩ := List.mem_iff_getElem.mp member
      obtain ⟨source,_,resident⟩ := inputs.get_right (index := index) (value := value)
        (by simpa only [List.getElem?_eq_getElem bound] using congrArg some found)
      exact World.stores_typed typed.roots resident

theorem NewValue.empty_worldTyped {program : Kernel.Program} {before after : World}
    {destination type head}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (notReference : ∀ id, head ≠ .reference id)
    (notPack : ∀ pack, head ≠ .bindings pack)
    (headTyped : Typing.ValueTyped program before (.resident before.nextOwner type head true []))
    (constructed : NewValue program.declarations before destination type head [] after) :
    Typing.WorldTyped program after := by
  apply constructed.worldTyped valid inventory typed
    (fun id impossible => False.elim (notReference id impossible))
    (fun pack impossible => False.elim (notPack pack impossible))
  intro values inputs
  cases inputs
  exact headTyped

theorem NewValue.callable_worldTyped {program : Kernel.Program} {before after : World}
    {destination id arguments function addresses}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (selected : Kernel.Instance program id arguments function)
    (captures : ListRel (fun formal address => ∃ value, before.Stores address value ∧ value.type = formal.type)
      function.captures addresses)
    (constructed : NewValue program.declarations before destination (.callable id arguments)
      (.callable id arguments) (addresses.map (fun address => ⟨address,.owner⟩)) after) :
    Typing.WorldTyped program after := by
  apply constructed.worldTyped valid inventory typed (by intros; contradiction) (by intros; contradiction)
  intro values inputs
  apply Typing.ValueTyped.callable selected
  have fieldTypes : ∀ (formals : List Kernel.Local) addresses values,
      ListRel (fun formal address => ∃ value, before.Stores address value ∧ value.type = formal.type) formals addresses →
      ListRel (fun (source : ResolvedPlace) value => before.Stores source.address value)
        (addresses.map (fun address => ⟨address,.owner⟩)) values →
      Typing.FieldsTyped program before (values.map some) (formals.map (·.type)) := by
    intro formals addresses values captures inputs
    induction captures generalizing values with
    | nil => cases inputs; exact .nil
    | cons first rest ih =>
      cases inputs with
      | cons stored tail =>
        obtain ⟨value,found,type⟩ := first
        have same := Option.some.inj (found.symm.trans stored)
        subst value
        exact .resident (World.stores_typed typed.roots stored) type (ih _ tail)
  exact fieldTypes _ _ _ captures inputs

namespace Execution

theorem ConstantValue.typed {program : Kernel.Program} {context : Language.Context}
    {next term finish value} (constructed : ConstantValue program.declarations context next term finish value)
    (world : World) : Typing.ValueTyped program world value := by
  refine ConstantValue.rec
    (motive_1 := fun _ _ _ value _ => Typing.ValueTyped program world value)
    (motive_2 := fun _ _ _ values _ =>
      Typing.FieldsTyped program world (values.map some) (values.map Value.type))
    ?_ ?_ ?_ ?_ ?_ ?_ constructed
  · intro next scalar valid
    exact .scalar valid
  · intro next
    exact .unit
  · intro next fields finish residents nonempty values typed
    exact .aggregate (Or.inl ⟨rfl,rfl,rfl⟩) typed
  · intro next id arguments fields finish residents type source values shape typed
    exact .aggregate shape typed
  · intro next
    exact .nil
  · intro next first rest middle finish value values constructed tail typed fields
    exact .resident typed rfl fields

theorem ConstantValue.bounds {program : Program} {context : Language.Context}
    {next term finish value} (constructed : ConstantValue program context next term finish value) :
    next < finish ∧ ∀ path resident, ResidentAt value path resident → next ≤ resident.owner ∧ resident.owner < finish := by
  refine ConstantValue.rec
    (motive_1 := fun next _ finish value _ => next < finish ∧
      ∀ path resident, ResidentAt value path resident → next ≤ resident.owner ∧ resident.owner < finish)
    (motive_2 := fun next _ finish values _ => next ≤ finish ∧
      ∀ (index : Nat) child, values[index]? = some child →
        ∀ path resident, ResidentAt child path resident → next ≤ resident.owner ∧ resident.owner < finish)
    ?_ ?_ ?_ ?_ ?_ ?_ constructed
  · intro next scalar valid
    refine ⟨Nat.lt_succ_self _,?_⟩
    intro path resident inside
    cases inside with
    | root => exact ⟨Nat.le_refl _,Nat.lt_succ_self _⟩
    | field selected nested => simp [Value.fields] at selected
  · intro next
    refine ⟨Nat.lt_succ_self _,?_⟩
    intro path resident inside
    cases inside with
    | root => exact ⟨Nat.le_refl _,Nat.lt_succ_self _⟩
    | field selected nested => simp [Value.fields] at selected
  · intro next fields finish residents nonempty values ih
    have bound : next < finish := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ih.1
    refine ⟨bound,?_⟩
    intro path resident inside
    cases inside with
    | root => exact ⟨Nat.le_refl _,bound⟩
    | field selected nested =>
      have found := ih.2 _ _ (by simpa [Value.fields] using selected) _ _ nested
      exact ⟨Nat.le_trans (Nat.le_succ _) found.1,found.2⟩
  · intro next id arguments fields finish residents type source values shape ih
    have bound : next < finish := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ih.1
    refine ⟨bound,?_⟩
    intro path resident inside
    cases inside with
    | root => exact ⟨Nat.le_refl _,bound⟩
    | field selected nested =>
      have found := ih.2 _ _ (by simpa [Value.fields] using selected) _ _ nested
      exact ⟨Nat.le_trans (Nat.le_succ _) found.1,found.2⟩
  · intro next
    exact ⟨Nat.le_refl _,fun _ _ impossible => by simp at impossible⟩
  · intro next first rest middle finish value values constructed tail ih later
    refine ⟨Nat.le_trans (Nat.le_of_lt ih.1) later.1,?_⟩
    intro index child selected path resident inside
    cases index with
    | zero =>
      have same := Option.some.inj selected
      subst child
      have range := ih.2 _ _ inside
      exact ⟨range.1,Nat.lt_of_lt_of_le range.2 later.1⟩
    | succ index =>
      have range := later.2 _ _ selected _ _ inside
      exact ⟨Nat.le_trans (Nat.le_of_lt ih.1) range.1,range.2⟩

theorem ConstantValues.bounds {program : Program} {context : Language.Context}
    {next terms finish values} (constructed : ConstantValues program context next terms finish values) :
    next ≤ finish ∧ ∀ (index : Nat) child, values[index]? = some child →
      ∀ path resident, ResidentAt child path resident → next ≤ resident.owner ∧ resident.owner < finish := by
  refine ConstantValues.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun next _ finish values _ => next ≤ finish ∧
      ∀ (index : Nat) child, values[index]? = some child →
        ∀ path resident, ResidentAt child path resident → next ≤ resident.owner ∧ resident.owner < finish)
    ?_ ?_ ?_ ?_ ?_ ?_ constructed
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro next
    exact ⟨Nat.le_refl _,fun _ _ impossible => by simp at impossible⟩
  · intro next first rest middle finish value values constructed tail _ later
    have ih := constructed.bounds
    refine ⟨Nat.le_trans (Nat.le_of_lt ih.1) later.1,?_⟩
    intro index child selected path resident inside
    cases index with
    | zero =>
      have same := Option.some.inj selected
      subst child
      have range := ih.2 _ _ inside
      exact ⟨range.1,Nat.lt_of_lt_of_le range.2 later.1⟩
    | succ index =>
      have range := later.2 _ _ selected _ _ inside
      exact ⟨Nat.le_trans (Nat.le_of_lt ih.1) range.1,range.2⟩

theorem ConstantValue.owner_unique {program : Program} {context : Language.Context}
    {next term finish value} (constructed : ConstantValue program context next term finish value) :
    ∀ left right x y, ResidentAt value left x → ResidentAt value right y → x.owner = y.owner → left = right := by
  have parent : ∀ (next : Nat) (type : Term) (head : ValueHead) (values : List Value),
      (∀ (index : Nat) child, values[index]? = some child →
        ∀ path resident, ResidentAt child path resident → next < resident.owner) →
      (∀ (first second : Nat) left right x y a b,
        values[first]? = some x → values[second]? = some y →
        ResidentAt x left a → ResidentAt y right b → a.owner = b.owner → first :: left = second :: right) →
      ∀ left right x y, ResidentAt (.resident next type head true (values.map some)) left x →
        ResidentAt (.resident next type head true (values.map some)) right y → x.owner = y.owner → left = right := by
    intro next type head values bounds unique left right x y first second same
    cases first with
    | root =>
      cases second with
      | root => rfl
      | field selected nested =>
        have greater := bounds _ _ (by simpa [Value.fields] using selected) _ _ nested
        change next = y.owner at same
        exact False.elim (Nat.ne_of_lt greater same)
    | field selected nested =>
      cases second with
      | root =>
        have greater := bounds _ _ (by simpa [Value.fields] using selected) _ _ nested
        change x.owner = next at same
        exact False.elim (Nat.ne_of_lt greater same.symm)
      | field other inside =>
        exact unique _ _ _ _ _ _ _ _ (by simpa [Value.fields] using selected)
          (by simpa [Value.fields] using other) nested inside same
  refine ConstantValue.rec
    (motive_1 := fun _ _ _ value _ =>
      ∀ left right x y, ResidentAt value left x → ResidentAt value right y → x.owner = y.owner → left = right)
    (motive_2 := fun _ _ _ values _ =>
      ∀ (first second : Nat) left right x y a b,
        values[first]? = some x → values[second]? = some y →
        ResidentAt x left a → ResidentAt y right b → a.owner = b.owner → first :: left = second :: right)
    ?_ ?_ ?_ ?_ ?_ ?_ constructed
  · intro next scalar valid
    exact parent _ _ _ [] (by intros; contradiction) (by intros; contradiction)
  · intro next
    exact parent _ _ _ [] (by intros; contradiction) (by intros; contradiction)
  · intro next fields finish residents nonempty values ih
    exact parent _ _ _ _ (fun index child found path resident inside =>
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (values.bounds.2 index child found path resident inside).1) ih
  · intro next id arguments fields finish residents type source values shape ih
    exact parent _ _ _ _ (fun index child found path resident inside =>
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (values.bounds.2 index child found path resident inside).1) ih
  · intro next first second left right x y a b found
    simp at found
  · intro next first rest middle finish value values constructed tail ih later
      firstIndex secondIndex left right x y a b first second atFirst atSecond same
    cases firstIndex with
    | zero =>
      have equal := Option.some.inj first
      subst x
      cases secondIndex with
      | zero =>
        have equal := Option.some.inj second
        subst y
        exact congrArg (List.cons 0) (ih _ _ _ _ atFirst atSecond same)
      | succ secondIndex =>
        have earlier := (constructed.bounds.2 _ _ atFirst).2
        have later := (tail.bounds.2 _ _ second _ _ atSecond).1
        rw [same] at earlier
        exact False.elim (Nat.not_lt_of_ge later earlier)
    | succ firstIndex =>
      cases secondIndex with
      | zero =>
        have equal := Option.some.inj second
        subst y
        have earlier := (constructed.bounds.2 _ _ atSecond).2
        have later := (tail.bounds.2 _ _ first _ _ atFirst).1
        rw [← same] at earlier
        exact False.elim (Nat.not_lt_of_ge later earlier)
      | succ secondIndex =>
        have equal := later _ _ _ _ _ _ _ _ first second atFirst atSecond same
        obtain ⟨indices,paths⟩ := List.cons.inj equal
        simp [indices,paths]

theorem ConstantValue.closed_heads {program : Program} {context : Language.Context}
    {next term finish value} (constructed : ConstantValue program context next term finish value) :
    ∀ path resident, ResidentAt value path resident →
      (∀ id, resident.head ≠ .reference id) ∧ (∀ pack, resident.head ≠ .bindings pack) := by
  refine ConstantValue.rec
    (motive_1 := fun _ _ _ value _ => ∀ path resident, ResidentAt value path resident →
      (∀ id, resident.head ≠ .reference id) ∧ (∀ pack, resident.head ≠ .bindings pack))
    (motive_2 := fun _ _ _ values _ => ∀ (index : Nat) child, values[index]? = some child →
      ∀ path resident, ResidentAt child path resident →
        (∀ id, resident.head ≠ .reference id) ∧ (∀ pack, resident.head ≠ .bindings pack))
    ?_ ?_ ?_ ?_ ?_ ?_ constructed
  · intro next scalar valid path resident inside
    cases inside with
    | root => simp [Value.head]
    | field selected nested => simp [Value.fields] at selected
  · intro next path resident inside
    cases inside with
    | root => simp [Value.head]
    | field selected nested => simp [Value.fields] at selected
  · intro next fields finish residents nonempty values ih path resident inside
    cases inside with
    | root => simp [Value.head]
    | field selected nested => exact ih _ _ (by simpa [Value.fields] using selected) _ _ nested
  · intro next id arguments fields finish residents type source values shape ih path resident inside
    cases inside with
    | root => simp [Value.head]
    | field selected nested => exact ih _ _ (by simpa [Value.fields] using selected) _ _ nested
  · intro next index child found
    simp at found
  · intro next first rest middle finish value values constructed tail ih later index child found path resident inside
    cases index with
    | zero =>
      have same := Option.some.inj found
      subst child
      exact ih _ _ inside
    | succ index => exact later _ _ found _ _ inside

theorem ConstantValue.install_worldTyped {program : Kernel.Program} {context : Language.Context}
    {before middle : World} {destination term finish value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (constructed : ConstantValue program.declarations context before.nextOwner term finish value)
    (vacant : before.Vacant destination)
    (located : AddressType program.declarations before destination value.type)
    (written : before.write destination (some value) = some middle) :
    Typing.WorldTyped program { middle with nextOwner := finish } := by
  have well := World.install_wellFormed typed.1 vacant (Nat.le_of_lt constructed.bounds.1)
    (fun path resident inside => (constructed.bounds.2 path resident inside).2) constructed.owner_unique
    (fun path resident inside address original stored same => by
      have fresh := (constructed.bounds.2 path resident inside).1
      have old := typed.1.2.2.2.2.2.2.1 address original stored
      rw [same] at fresh
      exact Nat.not_lt_of_ge fresh old)
    (fun path resident pack inside head => False.elim ((constructed.closed_heads path resident inside).2 pack head))
    (fun path resident id inside head => False.elim ((constructed.closed_heads path resident inside).1 id head)) written
  have retained : ∀ resident, Typing.ValueTyped program before resident →
      Typing.ValueTyped program { middle with nextOwner := finish } resident := by
    intro resident checked
    apply checked.transport (after := { middle with nextOwner := finish }) ?_ ?_ ?_
    · intro id loan found active
      refine ⟨by simpa only [World.write_loans written] using found,?_⟩
      intro type located
      exact ((World.write_address_types written (vacant.no_located_descendant
        (World.liveLoanLocations typed.1 _ _ found active))).mp located).retained
          (fun _ selected => selected) (fun _ => rfl)
    · have same := congrArg World.availability (World.write_rest written)
      exact same
    · intro pointer origin
      have retained := origin.transport (World.write_locations written)
      exact retained
  obtain ⟨offset,located⟩ := located
  have roots := World.write_typed_roots valid inventory typed.roots located written
    (fun resident same => by cases Option.some.inj same; exact ⟨constructed.typed before,rfl⟩)
  refine ⟨well,?_,?_,?_⟩
  · intro address resident stored
    exact retained _ (World.stores_typed roots (World.resident_iff_stores.mp stored))
  · intro id root resident found contents
    by_cases live : root.live = true
    · exact (roots id root resident found live contents).2
    · exact typed.2.2.1 id root resident (World.write_dead_root written found live) contents
  · apply World.root_regions_transport typed.2.2.2 (World.write_locations written)
    have same := congrArg World.nextRegion (World.write_rest written)
    exact Nat.le_of_eq same.symm

theorem DestinationType.vacant {world : World} {address type} (destination : DestinationType world address type) :
    world.Vacant address := by
  obtain ⟨empty,root,found,type,hole⟩ := destination
  exact ⟨root,found,Or.inl ⟨empty,hole⟩⟩

theorem DestinationType.addressType {program : Program} {world : World} {address type}
    (destination : DestinationType world address type) : AddressType program world address type := by
  obtain ⟨empty,root,found,type,hole⟩ := destination
  obtain ⟨found,live,generation⟩ := World.root_found found
  have same : address = ⟨address.root,root.generation,[]⟩ := by
    cases address
    simp_all
  rw [same,← type]
  exact ⟨0,.root found live⟩

/-- Every atomic producer preserves the complete storage invariant. This
consumes the actual construction/acquisition rules, not a typed post-state
admission hypothesis. Static-to-runtime equality coherence remains a separate
progress obligation. -/
theorem AtomStep.worldTyped {program : Kernel.Program} {before after : State} {event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (step : AtomStep program before event after) :
    Typing.WorldTyped program after.world := by
  cases step with
  | constant task constructed destination written =>
    exact constructed.install_worldTyped valid inventory typed destination.vacant destination.addressType written
  | acquire task resolved acquired => exact acquired.worldTyped valid inventory typed
  | borrow task resolved borrowed => exact borrowed.worldTyped valid inventory typed
  | construct task resolved inputs shape destination constructed =>
    exact constructed.aggregate_worldTyped valid inventory typed inputs shape
  | closure task selected captures inputs destination constructed =>
    exact constructed.callable_worldTyped valid inventory (captures.worldTyped valid inventory typed) selected inputs
  | function task selected empty destination constructed =>
    apply constructed.empty_worldTyped valid inventory typed (by simp) (by simp)
    exact .callable selected (by rw [empty]; exact .nil)
  | operation task selected constructed =>
    exact constructed.empty_worldTyped valid inventory typed (by simp) (by simp)
      (.operation selected)
  | label task found shape constructed =>
    apply constructed.empty_worldTyped valid inventory typed (by simp) (by simp)
    obtain ⟨region,result,type⟩ := shape
    rw [type]
    exact .label
  | primitive => exact typed

end Execution

end Glorious.Language
