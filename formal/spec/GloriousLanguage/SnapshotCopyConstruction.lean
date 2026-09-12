import GloriousLanguage.SnapshotReplayPreservation

/-! Constructive physical replay. `CopiesSnapshot` is a premise of the actual
replay rule, so this module produces its witness from real capture facts: the
finite identity inventory of the suspension is constructed from the actual
frames, saved homes, residents and loans, and the physical placement of the
copied storage is an ordered fold that either succeeds or reports genuine
physical exhaustion. -/
namespace Glorious.Language.Execution

open Kernel

/-- Identity-list deduplication with structural recursion, so that both its
membership and its distinctness are available without a termination proof.
This only deduplicates the finite inventory lists built below. -/
def distinctAux {α : Type} [DecidableEq α] (seen : List α) : List α → List α
  | [] => []
  | value :: rest => if value ∈ seen then distinctAux seen rest else value :: distinctAux (value :: seen) rest

def distinct {α : Type} [DecidableEq α] (values : List α) : List α := distinctAux [] values

theorem mem_distinctAux {α : Type} [DecidableEq α] {seen values : List α} {value : α} :
    value ∈ distinctAux seen values ↔ value ∈ values ∧ value ∉ seen := by
  induction values generalizing seen with
  | nil => simp [distinctAux]
  | cons head rest ih =>
      by_cases member : head ∈ seen
      · simp only [distinctAux,member,↓reduceIte,List.mem_cons]
        rw [ih]
        grind
      · simp only [distinctAux,member,↓reduceIte,List.mem_cons]
        rw [ih (seen := head :: seen)]
        grind

theorem distinctAux_nodup {α : Type} [DecidableEq α] {seen values : List α} :
    (distinctAux seen values).Nodup ∧ ∀ value ∈ distinctAux seen values, value ∉ seen := by
  induction values generalizing seen with
  | nil => exact ⟨by simp [distinctAux],by simp [distinctAux]⟩
  | cons head rest ih =>
      by_cases member : head ∈ seen
      · simpa only [distinctAux,member,↓reduceIte] using ih (seen := seen)
      · obtain ⟨restNodup,outside⟩ := ih (seen := head :: seen)
        simp only [distinctAux,member,↓reduceIte]
        refine ⟨List.nodup_cons.mpr ⟨?_,restNodup⟩,?_⟩
        · intro inside
          exact outside head inside (List.mem_cons_self ..)
        · intro value inside
          rcases List.mem_cons.mp inside with rfl | later
          · exact member
          · exact fun present => outside value later (List.mem_cons_of_mem _ present)

theorem mem_distinct {α : Type} [DecidableEq α] {values : List α} {value : α} :
    value ∈ distinct values ↔ value ∈ values := by
  rw [distinct,mem_distinctAux]
  simp

theorem distinct_nodup {α : Type} [DecidableEq α] (values : List α) :
    (distinct values).Nodup := (distinctAux_nodup (seen := []) (values := values)).1

/-- The activation recorded by an owning frame, if any. This only projects the
identity the existing home-ownership relation already names. -/
def Frame.activationSlot : Frame → Option Identity
  | .activation _ owner _ => some owner
  | _ => none

def Frame.scopeSlot : Frame → Option Identity
  | .scope _ owner _ => some owner
  | _ => none

def Frame.handlerIdentity : Frame → Option Identity
  | .handler installed _ => some installed.identity
  | _ => none

def Home.activationSlot : Home → Option Identity
  | .localSlot owner _ => some owner
  | .temporary owner _ => some owner
  | _ => none

def Home.scopeSlot : Home → Option Identity
  | .localSlot _ owner => some owner
  | .temporary _ owner => some owner
  | _ => none

theorem Frame.activationSlot_mem {frame : Frame} {owner : Identity} :
    Frame.activationSlot frame = some owner ↔
      ∃ caller region, frame = .activation caller owner region := by
  cases frame <;> simp [Frame.activationSlot]

theorem Frame.scopeSlot_mem {frame : Frame} {owner : Identity} :
    Frame.scopeSlot frame = some owner ↔ ∃ caller region, frame = .scope caller owner region := by
  cases frame <;> simp [Frame.scopeSlot]

theorem Frame.handlerIdentity_mem {frame : Frame} {identity : Identity} :
    Frame.handlerIdentity frame = some identity ↔
      ∃ installed owns, frame = .handler installed owns ∧ installed.identity = identity := by
  cases frame <;> simp [Frame.handlerIdentity]

theorem Home.activationSlot_mem {home : Home} {owner : Identity} :
    Home.activationSlot home = some owner ↔
      ∃ scope, home = .localSlot owner scope ∨ home = .temporary owner scope := by
  cases home <;> simp [Home.activationSlot]

theorem Home.scopeSlot_mem {home : Home} {owner : Identity} :
    Home.scopeSlot home = some owner ↔
      ∃ activation, home = .localSlot activation owner ∨ home = .temporary activation owner := by
  cases home <;> simp [Home.scopeSlot]

/-- The captured control regions: the owned regions of the saved frames, the
saved context region and the handler computation region. -/
def Suspension.controlRegions (suspension : Suspension) : List Identity :=
  suspension.frames.flatMap Frame.ownedRegions ++
    [suspension.context.region,suspension.handler.computation.region]

/-- The actual finite identity inventory of a suspension: the roots it captured,
the residents' owners, every shared loan of that resident graph, and the
storage/control regions, activations, scopes and handlers it holds. -/
noncomputable def Suspension.inventory (_program : Kernel.Program) (before : State)
    (suspension : Suspension) (physical : Table Nat) : Relocation := by
  classical
  exact
  { roots := suspension.roots
    owners := (List.range before.world.nextOwner).filter (fun id => decide
      (∃ address value, before.world.Resident address value ∧
        address.root ∈ suspension.roots ∧ value.owner = id))
    loans := (List.range before.world.nextLoan).filter (fun id => decide
      (SnapshotLoan before.world suspension.roots suspension.controlAuthoritySupport id))
    regions := distinct (suspension.controlRegions ++ suspension.roots.filterMap
      (fun id => (before.world.roots.get id).map Root.region))
    activations := distinct ((suspension.frames.filterMap Frame.activationSlot) ++ suspension.roots.filterMap
      (fun id => (suspension.homes.get id).bind Home.activationSlot))
    scopes := distinct ([suspension.handler.computation.scope] ++
      ((suspension.frames.filterMap Frame.scopeSlot) ++
        suspension.roots.filterMap (fun id => (suspension.homes.get id).bind Home.scopeSlot)))
    handlers := distinct (suspension.frames.filterMap Frame.handlerIdentity)
    rootBase := before.world.nextRoot
    ownerBase := before.world.nextOwner
    loanBase := before.world.nextLoan
    regionBase := before.world.nextRegion
    activationBase := before.nextActivation
    scopeBase := before.world.nextRegion
    handlerBase := before.nextHandler
    physical := physical }

theorem Suspension.inventory_roots {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).roots = suspension.roots := rfl

theorem Suspension.inventory_rootBase {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).rootBase = before.world.nextRoot := rfl

theorem Suspension.inventory_ownerBase {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).ownerBase = before.world.nextOwner := rfl

theorem Suspension.inventory_loanBase {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).loanBase = before.world.nextLoan := rfl

theorem Suspension.inventory_regionBase {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).regionBase = before.world.nextRegion := rfl

theorem Suspension.inventory_activationBase {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).activationBase = before.nextActivation := rfl

theorem Suspension.inventory_scopeBase {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).scopeBase = before.world.nextRegion := rfl

theorem Suspension.inventory_handlerBase {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).handlerBase = before.nextHandler := rfl

theorem Suspension.inventory_owners {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} {well : before.world.WellFormed} {id : Identity} :
    id ∈ (suspension.inventory program before physical).owners ↔ ∃ address value,
      before.world.Resident address value ∧ address.root ∈ suspension.roots ∧ value.owner = id := by
  classical
  simp only [Suspension.inventory,List.mem_filter,List.mem_range]
  constructor
  · intro member
    exact of_decide_eq_true member.2
  · rintro ⟨address,value,resident,member,owner⟩
    exact ⟨owner ▸ World.owner_bound well resident,decide_eq_true ⟨address,value,resident,member,owner⟩⟩

theorem Suspension.inventory_owners_nodup {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).owners.Nodup := by
  classical
  exact List.Nodup.sublist (List.filter_sublist (p := fun id => decide
    (∃ address value, before.world.Resident address value ∧
      address.root ∈ suspension.roots ∧ value.owner = id))) List.nodup_range

theorem Suspension.inventory_loans_nodup {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).loans.Nodup := by
  classical
  exact List.Nodup.sublist (List.filter_sublist (p := fun id => decide
    (SnapshotLoan before.world suspension.roots suspension.controlAuthoritySupport id))) List.nodup_range

theorem Suspension.inventory_loans {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} {well : before.world.WellFormed} {id : Identity} :
    id ∈ (suspension.inventory program before physical).loans ↔
      SnapshotLoan before.world suspension.roots suspension.controlAuthoritySupport id := by
  classical
  simp only [Suspension.inventory,List.mem_filter,List.mem_range]
  constructor
  · intro member
    exact of_decide_eq_true member.2
  · intro selected
    obtain ⟨loan,found,_,_⟩ := selected.record
    exact ⟨World.loanBounds well found,decide_eq_true selected⟩

theorem Suspension.inventory_regions {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} {id : Identity} :
    id ∈ (suspension.inventory program before physical).regions ↔
      id ∈ suspension.controlRegions ∨
        ∃ rootId root, rootId ∈ suspension.roots ∧ before.world.roots.get rootId = some root ∧
          root.region = id := by
  simp only [Suspension.inventory,mem_distinct,List.mem_append,List.mem_filterMap]
  constructor
  · rintro (control | ⟨rootId,member,chosen⟩)
    · exact Or.inl control
    · obtain ⟨root,found,equal⟩ := Option.map_eq_some_iff.mp chosen
      exact Or.inr ⟨rootId,root,member,found,equal⟩
  · rintro (control | ⟨rootId,root,member,found,equal⟩)
    · exact Or.inl control
    · exact Or.inr ⟨rootId,member,by rw [found]; exact congrArg some equal⟩

theorem Suspension.inventory_regions_nodup {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).regions.Nodup := distinct_nodup _

theorem Suspension.inventory_activations {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} {id : Identity} :
    id ∈ (suspension.inventory program before physical).activations ↔
      (∃ caller region, Frame.activation caller id region ∈ suspension.frames) ∨
        ∃ rootId home scope, rootId ∈ suspension.roots ∧ suspension.homes.get rootId = some home ∧
          (home = .localSlot id scope ∨ home = .temporary id scope) := by
  simp only [Suspension.inventory,mem_distinct,List.mem_append,List.mem_filterMap]
  constructor
  · rintro (⟨frame,member,chosen⟩ | ⟨rootId,member,chosen⟩)
    · obtain ⟨caller,region,shape⟩ := Frame.activationSlot_mem.mp chosen
      exact Or.inl ⟨caller,region,shape ▸ member⟩
    · obtain ⟨home,saved,chosen⟩ := Option.bind_eq_some_iff.mp chosen
      obtain ⟨scope,shape⟩ := Home.activationSlot_mem.mp chosen
      exact Or.inr ⟨rootId,home,scope,member,saved,shape⟩
  · rintro (⟨caller,region,member⟩ | ⟨rootId,home,scope,member,saved,shape⟩)
    · exact Or.inl ⟨.activation caller id region,member,Frame.activationSlot_mem.mpr ⟨caller,region,rfl⟩⟩
    · exact Or.inr ⟨rootId,member,by rw [saved]; exact Home.activationSlot_mem.mpr ⟨scope,shape⟩⟩

theorem Suspension.inventory_activations_nodup {program : Kernel.Program} {before : State}
    {suspension : Suspension} {physical : Table Nat} :
    (suspension.inventory program before physical).activations.Nodup := distinct_nodup _

theorem Suspension.inventory_scopes {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} {id : Identity} :
    id ∈ (suspension.inventory program before physical).scopes ↔
      id = suspension.handler.computation.scope ∨
        (∃ caller region, Frame.scope caller id region ∈ suspension.frames) ∨
        ∃ rootId home activation, rootId ∈ suspension.roots ∧ suspension.homes.get rootId = some home ∧
          (home = .localSlot activation id ∨ home = .temporary activation id) := by
  rw [Suspension.inventory,mem_distinct,List.mem_append,List.mem_append,List.mem_singleton,
    List.mem_filterMap,List.mem_filterMap]
  constructor
  · rintro (same | ⟨frame,member,chosen⟩ | ⟨rootId,member,chosen⟩)
    · exact Or.inl same
    · obtain ⟨caller,region,shape⟩ := Frame.scopeSlot_mem.mp chosen
      exact Or.inr (Or.inl ⟨caller,region,shape ▸ member⟩)
    · obtain ⟨home,saved,chosen⟩ := Option.bind_eq_some_iff.mp chosen
      obtain ⟨activation,shape⟩ := Home.scopeSlot_mem.mp chosen
      exact Or.inr (Or.inr ⟨rootId,home,activation,member,saved,shape⟩)
  · rintro (same | ⟨caller,region,member⟩ | ⟨rootId,home,activation,member,saved,shape⟩)
    · exact Or.inl same
    · exact Or.inr (Or.inl ⟨.scope caller id region,member,Frame.scopeSlot_mem.mpr ⟨caller,region,rfl⟩⟩)
    · exact Or.inr (Or.inr ⟨rootId,member,by rw [saved]; exact Home.scopeSlot_mem.mpr ⟨activation,shape⟩⟩)

theorem Suspension.inventory_scopes_nodup {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} :
    (suspension.inventory program before physical).scopes.Nodup := distinct_nodup _

theorem Suspension.inventory_handlers {program : Kernel.Program} {before : State} {suspension : Suspension}
    {physical : Table Nat} {id : Identity} :
    id ∈ (suspension.inventory program before physical).handlers ↔
      ∃ installed owns, Frame.handler installed owns ∈ suspension.frames ∧ installed.identity = id := by
  simp only [Suspension.inventory,mem_distinct,List.mem_filterMap]
  constructor
  · rintro ⟨frame,member,chosen⟩
    obtain ⟨installed,owns,shape,identity⟩ := Frame.handlerIdentity_mem.mp chosen
    exact ⟨installed,owns,shape ▸ member,identity⟩
  · rintro ⟨installed,owns,member,identity⟩
    exact ⟨.handler installed owns,member,Frame.handlerIdentity_mem.mpr ⟨installed,owns,rfl,identity⟩⟩

theorem Suspension.inventory_handlers_nodup {program : Kernel.Program} {before : State}
    {suspension : Suspension} {physical : Table Nat} :
    (suspension.inventory program before physical).handlers.Nodup := distinct_nodup _

end Glorious.Language.Execution
