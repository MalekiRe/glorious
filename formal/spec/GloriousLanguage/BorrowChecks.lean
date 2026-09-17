import GloriousLanguage.InvocationLending

/-! Execution witnesses at the invocation/pattern borrowing boundary. These
are not witnesses of whole-source semantic admission. -/
namespace Glorious.Language.BorrowChecks

open Kernel Execution

private def source : Address := ⟨0,0,[]⟩
private def handle : Address := ⟨1,0,[]⟩
private def unitValue : Value := .resident 0 .unit .unit true []
private def sourceRoot : Root :=
  ⟨.localSlot 0 0,0,0,1,⟨0,1,[],0,0,[]⟩,.unit,some unitValue,true,0,true,[]⟩
private def world : World :=
  { roots := [(0,sourceRoot)], liveRegions := [0,1], nextRoot := 1,
    nextOwner := 1, nextRegion := 2, clock := 1 }
private def context : Execution.Context := ⟨[],default,2,1,1,{},false,[]⟩
private def localSlot : Local := ⟨7,.reference .shared (.runtimeRegion 0) .unit,false⟩
private def referenceLayout : Layout := ⟨8,8,[],0,0,[]⟩
private def handleRoot : Root :=
  ⟨.localSlot 2 1,0,1,8,referenceLayout,localSlot.type,none,false,1,true,List.replicate 8 none⟩
private def allocated : World :=
  { world with roots := world.roots.set 1 handleRoot, nextRoot := 2, clock := 2 }
private def referenceValue : Value := .resident 1 localSlot.type (.reference 0) true []
private def borrowed : World :=
  { allocated with
    roots := allocated.roots.set 1 { handleRoot with value := some referenceValue }
    loans := [(0,⟨0,none,source,.shared,0,true,.restoring,[],false,none⟩)]
    nextOwner := 2
    nextLoan := 1 }

private theorem unitInitialized : unitValue.Initialized := by
  intro path resident location
  cases location with
  | root => simp [unitValue, Value.shellLive, Value.fields]
  | field member _ => simp [unitValue, Value.fields] at member

private theorem unitResident {path resident} (location : ResidentAt unitValue path resident) : resident = unitValue := by
  cases location with
  | root => rfl
  | field member _ => simp [unitValue, Value.fields] at member

private theorem ownedPermission (access : Access) : Permitted world .owner access source := by
  refine ⟨⟨sourceRoot,rfl⟩,?_⟩
  intro id loan found
  simp [world, Table.get] at found

/-- The former wrapper-only binding is rejected: real lending must create a
loan, regardless of whether the input was a capture or an explicit argument. -/
example (program : RuntimeProgram) (origin : InvocationOrigin) :
    ¬ BindsInput program 2 1 1 world ⟨origin,.resident ⟨9,.unit,false⟩,source,.owner,.shared⟩
      ⟨.localSlot 9,source,.shared .owner⟩ world := by
  intro bound
  obtain ⟨_,impossible⟩ := bound.lent_authority (by simp) (by trivial)
  cases impossible

example (program : RuntimeProgram) :
    ¬ BindsInput program 2 1 1 world ⟨.capture 0,.resident ⟨9,.unit,true⟩,source,.owner,.unique⟩
      ⟨.localSlot 9,source,.owner⟩ world := by
  intro bound
  obtain ⟨_,impossible⟩ := bound.lent_authority (by decide) (by trivial)
  cases impossible

example {program : RuntimeProgram} {activation scope region before input binding after}
    (shared : input.access = .shared)
    (bound : BindsInput program activation scope region before input binding after) :
    ¬ Permitted after binding.authority .owned binding.address ∧
    ¬ Permitted after binding.authority .unique binding.address := by
  exact ⟨bound.shared_no_mutation shared (by decide),bound.shared_no_mutation shared (by decide)⟩

example {program : RuntimeProgram} {activation scope region before input binding after}
    (resident : input.formal.IsResident)
    (bound : BindsInput program activation scope region before input binding after) :
    ∃ value, before.Stores input.storage value ∧ value.type = input.formal.type := by
  cases bound <;> simp_all [InputFormal.IsResident] <;> exact ⟨_,by assumption,by assumption⟩

example (map : Relocation) (id : Identity) :
    map.authority (.shared (.loan id)) = .shared (.loan (map.loan id)) := rfl

example (world : World) (handle : Address) (backing : Authority) (id : Identity) :
    ReferenceView world handle (.shared backing) id .unique ((.shared backing : Authority).referenceView id .shared) .shared := by
  refine Or.inr (Or.inr ⟨rfl,?_,rfl,rfl⟩)
  intro permission
  cases shared_authority_cannot_strengthen permission

example {world handle backing id mode permission} :
    ¬ ReferenceView world handle (.shared backing) id mode permission .unique := by
  intro view
  cases reference_view_shared_carrier view

/-- The ordinary projection consumer cannot remove the input's access cap
merely by finding a unique reference value in its storage. -/
example {world : World} {environment : Environment} {handle : Address} {backing : Authority} {id : Identity}
    {value : Value} {loan : Loan}
    (stored : world.Stores handle value) (head : value.head = .reference id)
    (initialized : value.Initialized) (readable : Permitted world (.shared backing) .shared handle)
    (found : world.loans.get id = some loan) (live : loan.live = true) (unique : loan.mode = .unique) :
    ResolvesProjections world environment handle (.shared backing) [.dereference] loan.referent
      ((.shared backing : Authority).referenceView id .shared) := by
  refine .dereference (access := .shared) stored head initialized readable found live ?_ .nil
  refine Or.inr (Or.inr ⟨unique,?_,rfl,rfl⟩)
  intro permission
  cases shared_authority_cannot_strengthen permission

private theorem allocateHandle {program : Language.Program}
    (pointer : program.input.target.pointerBits = 64)
    (capacity : 8 ≤ program.input.target.maximumObjectBytes) :
    Allocates program world (.localSlot 2 1) 1 localSlot.type referenceLayout false handle allocated := by
  refine .fresh (base := 8) ⟨by decide,?_,⟨⟨3,rfl⟩,by decide,by simp [referenceLayout]⟩,capacity,
    ⟨default,false,?_⟩⟩ ⟨by decide,by decide,?_,?_⟩
  · intro id occurs
    change Occurs (.runtimeRegion id) (.reference .shared (.runtimeRegion 0) .unit) at occurs
    cases occurs with
    | child member occurs =>
      simp only [Term.children,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · cases occurs with
        | here => decide
        | child member _ => simp [Term.children] at member
      · cases occurs with
        | child member _ => simp [Term.children] at member
  · simpa [localSlot, referenceLayout, pointer] using
      (@LayoutOf.reference program ⟨[],[],0,default,false,{}⟩ .shared (.runtimeRegion 0) .unit)
  · simp [referenceLayout, pointer]
  · intro id root found _
    simp [world, Table.get] at found
    obtain ⟨rfl,rfl⟩ := found
    exact Or.inr (Or.inl rfl)

private theorem unitReachable {state : World} {authority current : Authority} {incoming access : Access}
    {resident : Value} (reachable : unitValue.ReachableResident state authority incoming resident current access) :
    resident = unitValue := by
  induction reachable with
  | resident location => exact unitResident location
  | referent _ head _ _ _ ih => simp [ih,unitValue,Value.head] at head
  | resource _ member _ _ ih => simp [ih,unitValue,Value.resources] at member

private theorem unitNoReference {state : World} {authority current : Authority} {incoming access : Access}
    {identity : Identity} : ¬ unitValue.ReachableReference state authority incoming identity current access := by
  rintro ⟨resident,reachable,head⟩
  simp [unitReachable reachable,unitValue,Value.head] at head

private theorem unitAccessible (program : RuntimeProgram) (state : World) (access : Access) :
    unitValue.ResourcesAccessible program state access := by
  refine ⟨?_,?_,?_,?_⟩
  · intro resident authority incoming reachable
    rw [unitReachable reachable]
    exact ⟨by simp [unitValue,Value.resources],rfl⟩
  · intro identity authority incoming reachable
    exact False.elim (unitNoReference reachable)
  · intro identity authority incoming reachable
    exact False.elim (unitNoReference reachable)
  · intro resident authority incoming reachable binding member
    simp [unitReachable reachable,unitValue,Value.resources] at member

private theorem borrowHandle (program : RuntimeProgram) :
    Borrows program allocated .owner .shared 0 source handle borrowed := by
  refine .borrow (purpose := .source) (before := allocated) (authority := .owner) (mode := .shared) (region := 0)
    (referent := source) (destination := handle) (value := unitValue) (parent := none) rfl
    ⟨0,.root (root := sourceRoot) (id := 0) rfl rfl⟩ unitInitialized
    (by decide) (show Addressable program.declarations ⟨[],[],0,default,false,{}⟩ .unit from .unit)
    (unitAccessible program allocated .shared) ?_ ⟨handleRoot,rfl,Or.inl ⟨rfl,rfl⟩⟩
    ⟨0,.root (root := handleRoot) (id := 1) rfl rfl⟩ rfl rfl
  refine ⟨⟨sourceRoot,rfl⟩,?_⟩
  intro id loan found
  simp [allocated, world, Table.get] at found

/-- A pattern local owns an actual typed reference handle. Its referent is
the old storage and its loan uses the declared region, not the handle's slot
region. This is the real machine binding step, not just a type projection. -/
example {program : Kernel.Program} (pointer : program.declarations.input.target.pointerBits = 64)
    (capacity : 8 ≤ program.declarations.input.target.maximumObjectBytes) (body : Code) :
    LocalStep program
      { world := world, task := .pattern context [.bind localSlot source .owner .shared] body }
      none
      { world := borrowed, task := .pattern (context.bind localSlot handle .owner) [] body } := by
  have bound : BindsPattern program 2 1 1 world localSlot source .owner .shared
      ⟨.localSlot 7,handle,.owner⟩ borrowed :=
    .borrowed (before := world) (source := source) (localSlot := localSlot) (mode := .shared)
      (loanRegion := 0) (value := unitValue) rfl rfl (allocateHandle pointer capacity) (borrowHandle _)
  exact .patternBind (context := context)
    (before := { world := world, task := .pattern context [.bind localSlot source .owner .shared] body }) rfl bound

example (program : Kernel.Program) :
    borrowed.Stores handle referenceValue ∧ Typing.ValueTyped program borrowed referenceValue := by
  refine ⟨rfl,?_⟩
  exact .reference (loan := ⟨0,none,source,.shared,0,true,.restoring,[],false,none⟩) rfl rfl rfl rfl
    ⟨0,.root (root := sourceRoot) (id := 0) rfl rfl⟩

example (program : Kernel.Program) :
    Typing.PatternType program.declarations ⟨[],[],0,default,false,{}⟩
      (.reference .unique (.bind localSlot)) (.reference .unique (.runtimeRegion 0) .unit) .shared [localSlot] := by
  apply Typing.PatternType.reference
  exact .borrowBind (mode := .shared) rfl .runtimeRegion

private def parent : Loan := ⟨0,none,source,.unique,0,true,.restoring,[],false,none⟩
private def child : Loan := ⟨1,some 0,source,.shared,1,true,.restoring,[],false,none⟩
private def pinned : World := { world with loans := [(1,child),(0,parent)], nextLoan := 2 }
private def childEnded : World := { pinned with loans := pinned.loans.set 1 { child with live := false } }
private def allEnded : World := { childEnded with loans := childEnded.loans.set 0 { parent with live := false } }

private theorem noHandles {state : World} (roots : state.roots = world.roots) (id : Identity) :
    ¬ state.References id := by
  rintro ⟨address,value,resides,head⟩
  rcases resides with ⟨root,whole,found,_,_,resident,location⟩
  rw [roots] at found
  simp [world, Table.get] at found
  obtain ⟨_,rfl⟩ := found
  simp [sourceRoot] at resident
  subst whole
  have same := unitResident location
  subst value
  simp [unitValue, Value.head] at head

private theorem unitWorldClosed (program : RuntimeProgram) {state : World}
    (stored : state.Stores source unitValue) : state.ResourcesClosed program source := by
  intro value found
  have same : value = unitValue := Option.some.inj (found.symm.trans stored)
  subst value
  exact ⟨(unitAccessible program state .shared).1,(unitAccessible program state .shared).2.1⟩

private theorem noResourceHandles {state : World} (roots : state.roots = world.roots) (id : Identity) :
    ¬ state.ResourceReferences id := by
  rintro ⟨address,value,binding,resides,member,_⟩
  rcases resides with ⟨root,whole,found,_,_,resident,location⟩
  rw [roots] at found
  simp [world,Table.get] at found
  obtain ⟨_,rfl⟩ := found
  simp [sourceRoot] at resident
  subst whole
  simp [unitResident location,unitValue,Value.resources] at member

private theorem endChild (program : RuntimeProgram) : EndsLoan program pinned 1 childEnded := by
  refine .restored (loan := child) rfl rfl (Or.inl rfl) ⟨unitValue,rfl,unitInitialized⟩
    (fun _ => unitWorldClosed program rfl) (noHandles rfl 1) (noResourceHandles rfl 1) ?_
  intro other found ancestry
  by_cases first : other.identity = 1
  · have equal : child = other := Option.some.inj (by simpa [pinned, Table.get, first] using found)
    subst other
    simp [child] at ancestry
  · by_cases second : other.identity = 0
    · have equal : parent = other := Option.some.inj (by simpa [pinned, Table.get, second] using found)
      subst other
      simp [parent] at ancestry
    · simp [pinned, Table.get, Ne.symm first, Ne.symm second] at found

private theorem endParent (program : RuntimeProgram) : EndsLoan program childEnded 0 allEnded := by
  refine .restored (loan := parent) rfl rfl (Or.inl rfl) ⟨unitValue,rfl,unitInitialized⟩
    (fun _ => unitWorldClosed program rfl) (noHandles rfl 0) (noResourceHandles rfl 0) ?_
  intro other found ancestry
  by_cases first : other.identity = 1
  · have equal : { child with live := false } = other :=
      Option.some.inj (by simpa [childEnded, Table.get, Table.set, first] using found)
    subst other
    rfl
  · by_cases second : other.identity = 0
    · have equal : parent = other := Option.some.inj (by
        simpa [childEnded, pinned, Table.get, Table.set, Table.erase, second] using found)
      subst other
      simp [parent] at ancestry
    · simp [childEnded, pinned, Table.get, Table.set, Table.erase, Ne.symm first, Ne.symm second] at found

/-- Removing the last parent handle defers retirement while a child is live;
ending the child then releases the orphaned parent through the same task on
normal cleanup, cancellation and label-exit cleanup paths. -/
example (program : Kernel.Program) (next : Task) :
    LocalStep program { world := pinned, task := .releaseLoan 0 next } none
      { world := pinned, task := next } :=
  .releaseBorrowed rfl (noHandles rfl 0) (child := child) rfl (Or.inl rfl) rfl

example (program : Kernel.Program) (next : Task) :
    LocalStep program { world := pinned, task := .releaseLoan 1 next } (some (.loanEnd 1))
      { world := childEnded, task := .releaseLoan 0 next } :=
  .releaseChild rfl (loan := child) rfl rfl (endChild program)

example (program : Kernel.Program) (next : Task) :
    LocalStep program { world := childEnded, task := .releaseLoan 0 next } (some (.loanEnd 0))
      { world := allEnded, task := next } :=
  .releaseRoot rfl (loan := parent) rfl rfl (endParent program)

example (program : RuntimeProgram) (after : World) : ¬ EndsLoan program pinned 0 after := by
  intro ended
  cases ended with
  | restored found _ _ _ _ _ _ children =>
      have same : parent = _ := Option.some.inj found
      subst_vars
      have impossible := children child rfl (Or.inl rfl)
      cases impossible

private def replayParent : Loan := { parent with mode := .shared }
private def childReference : Value :=
  .resident 1 (.reference .shared (.runtimeRegion 1) .unit) (.reference 1) true []
private def replayHandle : Root := { handleRoot with type := childReference.type, value := some childReference }
private def replayWorld : World :=
  { borrowed with roots := [(0,sourceRoot),(1,replayHandle)], loans := [(1,child),(0,replayParent)], nextLoan := 2 }

/-- Only the child's handle is resident, but snapshot selection includes the
live, shared parent. The copied graph therefore retains its cleanup ancestry. -/
example : SnapshotLoan replayWorld [0,1] [] 0 := by
  have selected : SnapshotLoan replayWorld [0,1] [] 1 :=
    .reference (loan := child) (address := handle) (value := childReference)
      rfl rfl rfl (by decide) ⟨replayHandle,childReference,rfl,rfl,rfl,rfl,.root⟩ rfl
  exact .parent (loan := child) (ancestor := replayParent) selected rfl rfl rfl rfl rfl

example (map : Relocation) :
    (map.loanValue child).parent = some (map.loan 0) := by
  simp [Relocation.loanValue, child]

end Glorious.Language.BorrowChecks
