import GloriousLanguage.TransferPreservation

/-! Nonvacuous storage witnesses for the preservation proof. In particular,
an extant unique reference survives a real move-and-restore sequence. -/
namespace Glorious.Language.PreservationChecks

open Kernel Execution

private def source : Address := ⟨0,0,[]⟩
private def destination : Address := ⟨1,0,[]⟩
private def handle : Address := ⟨2,0,[]⟩
private def unitValue : Value := .resident 0 .unit .unit true []
private def referenceType : Term := .reference .unique (.runtimeRegion 0) .unit
private def referenceValue : Value := .resident 1 referenceType (.reference 0) true []
private def sourceRoot : Root :=
  ⟨.localSlot 0 0,0,0,1,⟨0,1,[],0,0,[]⟩,.unit,some unitValue,true,0,true,[]⟩
private def vacantRoot : Root := { sourceRoot with value := none }
private def handleRoot : Root :=
  ⟨.localSlot 0 0,0,0,8,⟨8,8,[],0,0,[]⟩,referenceType,some referenceValue,false,1,true,List.replicate 8 none⟩
private def loan : Loan := ⟨0,none,source,.unique,0,true,.restoring,[],false,none⟩
private def world : World :=
  { roots := [(0,sourceRoot),(1,vacantRoot),(2,handleRoot)], loans := [(0,loan)],
    liveRegions := [0], nextRoot := 3, nextOwner := 2, nextLoan := 1, nextRegion := 1, clock := 3 }
private def cleared : World := { world with roots := world.roots.set 0 vacantRoot }
private def moved : World := { cleared with roots := cleared.roots.set 1 sourceRoot }
private def restoreCleared : World := { moved with roots := moved.roots.set 1 vacantRoot }

private theorem initialized : unitValue.Initialized := by
  intro path value location
  cases location with
  | root => simp [unitValue, Value.shellLive, Value.fields]
  | field member _ => simp [unitValue, Value.fields] at member

private theorem roots {id root} (found : world.roots.get id = some root) :
    (id = 0 ∧ root = sourceRoot) ∨ (id = 1 ∧ root = vacantRoot) ∨ (id = 2 ∧ root = handleRoot) := by
  have member := Table.mem_of_get found
  simpa [world] using member

private theorem leaf {value : Value} {path : List Nat} {resident : Value}
    (empty : value.fields = []) (location : ResidentAt value path resident) : path = [] ∧ resident = value := by
  cases location with
  | root => exact ⟨rfl,rfl⟩
  | field member _ => simp [empty] at member

private theorem occupants {address value} (resident : world.Resident address value) :
    (address = source ∧ value = unitValue) ∨ (address = handle ∧ value = referenceValue) := by
  rcases resident with ⟨root,whole,found,_,generation,stored,location⟩
  rcases roots found with ⟨key,rfl⟩ | ⟨key,rfl⟩ | ⟨key,rfl⟩
  · have same : whole = unitValue := by simpa [sourceRoot] using stored.symm
    subst whole
    obtain ⟨path,rfl⟩ := leaf rfl location
    exact Or.inl ⟨by cases address; simp_all [source, sourceRoot],rfl⟩
  · simp [vacantRoot] at stored
  · have same : whole = referenceValue := by simpa [handleRoot] using stored.symm
    subst whole
    obtain ⟨path,rfl⟩ := leaf rfl location
    exact Or.inr ⟨by cases address; simp_all [handle, handleRoot],rfl⟩

private theorem worldValid : world.WellFormed := by
  refine ⟨by simp [world,Table.Unique],by simp [world,Table.Unique],by simp [world,Table.Unique],by decide,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro id available found
    simp [world,Table.get] at found
  · intro address value pack resident head
    rcases occupants resident with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases head
  · intro address value resident
    rcases occupants resident with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  · intro a b left right first second same
    rcases occupants first with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases occupants second with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> first | rfl | cases same
  · intro id root found
    rcases roots found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [world,sourceRoot,vacantRoot,handleRoot,Layout.Valid,PowerOfTwo] <;>
      first | exact ⟨0,rfl⟩ | exact ⟨3,rfl⟩
  · intro region member
    simp [world] at member
    subst region
    decide
  · intro id root found _
    rcases roots found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  · intro a b left right first second different _ _
    rcases roots first with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases roots second with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      first | exact False.elim (different rfl) | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
  · intro id resident found
    have member := Table.mem_of_get found
    simp [world] at member
    obtain ⟨rfl,rfl⟩ := member
    exact ⟨rfl,by decide,fun _ => ⟨by decide,by decide⟩⟩
  · intro address value id resident head
    rcases occupants resident with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · cases head
    · have same : id = 0 := by simpa [referenceValue,Value.head] using head.symm
      subst id
      exact ⟨loan,rfl,rfl⟩
  · intro a b left right first second _ _ _ _
    have firstMember := Table.mem_of_get first
    have secondMember := Table.mem_of_get second
    simp [world] at firstMember secondMember
    obtain ⟨rfl,rfl⟩ := firstMember
    obtain ⟨rfl,rfl⟩ := secondMember
    exact Or.inl .refl
  · intro id resident parent found selected
    have member := Table.mem_of_get found
    simp [world] at member
    obtain ⟨rfl,rfl⟩ := member
    cases selected
  · intro id resident found _
    have member := Table.mem_of_get found
    simp [world] at member
    obtain ⟨rfl,rfl⟩ := member
    exact Or.inl ⟨unitValue,rfl⟩
  · intro id resident guard found member
    have selected := Table.mem_of_get found
    simp [world] at selected
    obtain ⟨rfl,rfl⟩ := selected
    simp [loan] at member
  · intro id resident found
    have selected := Table.mem_of_get found
    simp [world] at selected
    obtain ⟨rfl,rfl⟩ := selected
    simp [Loan.KindValid,LoanKind.Allows,loan]

private theorem referenceTyped (program : Kernel.Program) : Typing.ValueTyped program world referenceValue :=
  .reference (loan := loan) rfl rfl rfl rfl ⟨0,.root (root := sourceRoot) (id := 0) rfl rfl⟩

private theorem worldTyped (program : Kernel.Program)
    (pointer : program.declarations.input.target.pointerBits = 64) : Typing.WorldTyped program world := by
  refine ⟨worldValid,?_,?_,?_,?_⟩
  · intro address value resident
    rcases occupants resident with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .unit
    · exact referenceTyped program
  · intro id root value found stored
    rcases roots found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [sourceRoot,vacantRoot,handleRoot] at stored <;> subst value <;> rfl
  · intro id root found
    rcases roots found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · intro region occurs
      cases occurs with
      | child member _ => simp [sourceRoot,Term.children] at member
    · intro region occurs
      cases occurs with
      | child member _ => simp [vacantRoot,sourceRoot,Term.children] at member
    · intro region occurs
      cases occurs with
      | child member occurs =>
        simp [handleRoot,referenceType,Term.children] at member
        rcases member with rfl | rfl
        · cases occurs with
          | here => decide
          | child member _ => simp [Term.children] at member
        · cases occurs with
          | child member _ => simp [Term.children] at member
  · intro id root found live
    rcases roots found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .unit
    · exact .unit
    · simpa [handleRoot,referenceType,pointer] using
        (LayoutOf.reference (program := program.declarations) (context := ⟨[],[],0,default,false,{}⟩)
          (mode := .unique) (region := .runtimeRegion 0) (referent := .unit))

private theorem unitResident {resident : Value} {path : List Nat}
    (location : ResidentAt unitValue path resident) : resident = unitValue := by
  cases location with
  | root => rfl
  | field member _ => simp [unitValue,Value.fields] at member

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

private theorem unitReady (program : RuntimeProgram) (state : World) (footprint : List Address) :
    unitValue.MoveReady program state footprint := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro resident authority incoming reachable
    rw [unitReachable reachable]
    exact ⟨by simp [unitValue,Value.resources],rfl⟩
  · intro identity authority incoming reachable
    exact False.elim (unitNoReference reachable)
  · intro identity authority incoming reachable
    exact False.elim (unitNoReference reachable)
  · intro resident authority incoming reachable binding member
    simp [unitReachable reachable,unitValue,Value.resources] at member
  · intro source _ address support
    rcases support with ⟨resident,authority,access,reachable,observed⟩
    rcases observed with ⟨identity,loan,reference,found,referent⟩ | ⟨binding,member,addressEq⟩
    · simp [unitReachable reachable,unitValue,Value.head] at reference
    · simp [unitReachable reachable,unitValue,Value.resources] at member

private theorem sourceStored : world.Stores source unitValue := rfl

private theorem restoredStored : moved.Stores destination unitValue := rfl

private theorem move (program : RuntimeProgram) : Transfers program world (.loan 0) source destination moved := by
  refine .move (value := unitValue) (cleared := cleared) sourceStored initialized (unitReady program world _) ?_
    ⟨vacantRoot,rfl,Or.inl ⟨rfl,rfl⟩⟩ (by simp [source,destination,Address.Overlaps])
    ⟨0,.root (root := vacantRoot) (id := 1) rfl rfl⟩ rfl rfl
  refine ⟨⟨sourceRoot,rfl⟩,loan,rfl,rfl,rfl,rfl,⟨[],rfl⟩,(fun _ => rfl),?_,?_,?_⟩
  · intro other resident found _ different
    have member := Table.mem_of_get found
    simp [world] at member
    exact False.elim (different member.1)
  · simp [loan]
  · intro other resident found _ guarded
    have member := Table.mem_of_get found
    simp [world] at member
    obtain ⟨rfl,rfl⟩ := member
    simp [loan] at guarded

private theorem restore (program : RuntimeProgram) : Transfers program moved .owner destination source world := by
  refine .move (value := unitValue) (cleared := restoreCleared) restoredStored initialized (unitReady program moved _) ?_
    ⟨vacantRoot,rfl,Or.inl ⟨rfl,rfl⟩⟩ (by simp [source,destination,Address.Overlaps])
    ⟨0,.root (root := vacantRoot) (id := 0) rfl rfl⟩ rfl rfl
  refine ⟨⟨sourceRoot,rfl⟩,?_⟩
  intro id resident found _ overlap
  have member := Table.mem_of_get found
  simp [moved,cleared,world] at member
  obtain ⟨rfl,rfl⟩ := member
  simp [source,destination,loan,Address.Overlaps] at overlap

/-- A reference remains typed while its referent is temporarily vacant.
Reading the vacant referent and ending its loan are still forbidden. -/
example (program : Kernel.Program) :
    Transfers program.toRuntimeProgram world (.loan 0) source destination moved ∧
    moved.Stores handle referenceValue ∧ Typing.ValueTyped program moved referenceValue ∧
    moved.Vacant source ∧ ¬ moved.Initialized source ∧
    (∀ after, ¬ EndsLoan program.toRuntimeProgram moved 0 after) ∧ Transfers program.toRuntimeProgram moved .owner destination source world := by
  refine ⟨move _,rfl,(move program.toRuntimeProgram).reference_preserved worldValid (referenceTyped program),
    ⟨vacantRoot,rfl,Or.inl ⟨rfl,rfl⟩⟩,?_,?_,restore _⟩
  · rintro ⟨value,stored,_⟩
    cases stored
  · intro after
    exact hole_cannot_end (loan := loan) rfl (by rintro ⟨value,stored,_⟩; cases stored)

example (program : Kernel.Program) : moved.LoanParents ∧ moved.LiveLoanLocations ∧
    Typing.ValueTyped program moved referenceValue :=
  ⟨(move program.toRuntimeProgram).loanParents (World.loanParents worldValid),
    (move program.toRuntimeProgram).liveLoanLocations worldValid,
    (referenceTyped program).transfer worldValid (move program.toRuntimeProgram)⟩

example (program : Kernel.Program) (valid : ProgramWellFormed program.declarations)
    (inventory : BodyInventory program) (pointer : program.declarations.input.target.pointerBits = 64) :
    ∀ address value, moved.Resident address value → Typing.ValueTyped program moved value :=
  ((move program.toRuntimeProgram).typed_residents valid inventory (worldTyped program pointer)).1

example (program : Kernel.Program) (valid : ProgramWellFormed program.declarations)
    (inventory : BodyInventory program) (pointer : program.declarations.input.target.pointerBits = 64) :
    Typing.WorldTyped program moved ∧ Typing.WorldTyped program world := by
  have movedTyped := (move program.toRuntimeProgram).worldTyped valid inventory (worldTyped program pointer)
  exact ⟨movedTyped,(restore program.toRuntimeProgram).worldTyped valid inventory movedTyped⟩

private def duplicated : World := { world with roots := world.roots.set 1 sourceRoot }

/-- Copying the bytes/tree without clearing the source would duplicate the
same logical owner, despite both unit residents being well typed. -/
example : world.write destination (some unitValue) = some duplicated ∧ ¬ duplicated.WellFormed := by
  refine ⟨rfl,?_⟩
  intro valid
  have sourceResident : duplicated.Resident source unitValue := ⟨sourceRoot,unitValue,rfl,rfl,rfl,rfl,.root⟩
  have destinationResident : duplicated.Resident destination unitValue := ⟨sourceRoot,unitValue,rfl,rfl,rfl,rfl,.root⟩
  have impossible := valid.2.2.2.2.2.2.2.1 source destination unitValue unitValue sourceResident destinationResident rfl
  cases impossible

private def cyclic : World := { world with loans := [(0,{ loan with parent := some 0 })] }

example : ¬ cyclic.WellFormed := by
  intro valid
  obtain ⟨_,_,impossible,_⟩ := World.loanParents valid 0 { loan with parent := some 0 } 0 rfl rfl
  exact Nat.lt_irrefl 0 impossible

example (program : Kernel.Program) (host : Foreign.Model) (next : Task) :
    Run program host
      { world := world, task := .transfer source (.loan 0) destination (.transfer destination .owner source next) }
      [.move source destination,.move destination source]
      { world := world, task := next } := by
  apply Run.visible (middle := { world := moved, task := .transfer destination .owner source next })
  · exact Or.inl (.transfer rfl (move _))
  · apply Run.visible (middle := { world := world, task := next })
    · exact Or.inl (.transfer rfl (restore _))
    · exact .refl

private def badRoot : Root :=
  { vacantRoot with type := .scalar (.integer false (.fixed 8)), layout := ⟨1,1,[],0,0,[]⟩, bytes := [none] }
private def badWorld : World := { world with roots := world.roots.set 1 badRoot }

private theorem noUnitDestination (program : Language.Program) : ¬ AddressType program badWorld destination .unit := by
  intro typed
  rcases (AddressType.root_iff rfl).mp typed with ⟨root,found,typeEq⟩
  have actual : badWorld.root destination = some badRoot := rfl
  have same : root = badRoot := Option.some.inj (found.symm.trans actual)
  subst root
  cases typeEq

example (program : RuntimeProgram) (after : World) :
    ¬ Transfers program badWorld (.loan 0) source destination after := by
  intro transfer
  exact noUnitDestination program.declarations (transfer.destination_type (value := unitValue) rfl)

example (program : RuntimeProgram) (after : World) :
    ¬ Copies program badWorld (.loan 0) source destination after := by
  intro copy
  exact noUnitDestination program.declarations (copy.destination_type (value := unitValue) rfl)

example (program : RuntimeProgram) (after : World) :
    ¬ NewValue program badWorld destination .unit .unit [] after := by
  intro constructed
  exact noUnitDestination program.declarations constructed.destination_type

namespace Nested

private def source : Address := ⟨0,0,[0,0]⟩
private def destination : Address := ⟨0,0,[1]⟩
private def innerType : Term := .tuple [.unit]
private def outerType : Term := .tuple [innerType,.unit]
private def inner : Value := .resident 3 innerType .tuple true [some unitValue]
private def innerHole : Value := inner.withFields [none]
private def outer : Value := .resident 2 outerType .tuple true [some inner,none]
private def clearedValue : Value := outer.withFields [some innerHole,none]
private def movedValue : Value := outer.withFields [some innerHole,some unitValue]
private def root : Root := { sourceRoot with type := outerType, value := some outer, layout := ⟨0,1,[0,0],0,0,[]⟩ }
private def loan : Loan := ⟨0,none,source,.unique,0,true,.restoring,[],false,none⟩
private def world : World :=
  { PreservationChecks.world with roots := [(0,root),(2,handleRoot)], loans := [(0,loan)], nextOwner := 4 }
private def cleared : World := { world with roots := world.roots.set 0 { root with value := some clearedValue } }
private def moved : World := { world with roots := world.roots.set 0 { root with value := some movedValue } }

private theorem zeroValid : (⟨0,1,[],0,0,[]⟩ : Layout).Valid := ⟨⟨0,rfl⟩,rfl,by simp⟩
private theorem innerLayout : AggregateLayout [⟨0,1,[],0,0,[]⟩] ⟨0,1,[0],0,0,[]⟩ :=
  ⟨0,.cons zeroValid .nil,rfl,rfl,rfl,rfl,rfl⟩
private theorem outerLayout : AggregateLayout [⟨0,1,[0],0,0,[]⟩,⟨0,1,[],0,0,[]⟩] ⟨0,1,[0,0],0,0,[]⟩ :=
  ⟨0,.cons ⟨⟨0,rfl⟩,rfl,by simp⟩ (.cons zeroValid .nil),rfl,rfl,rfl,rfl,rfl⟩

private theorem sourceTyped (program : Language.Program) : AddressType program world source .unit := by
  have base : AddressOffset program world ⟨0,0,[]⟩ outerType 0 := .root (root := root) rfl rfl
  have first : AddressOffset program world ⟨0,0,[0]⟩ innerType 0 :=
    .child (index := 0) base (.tuple rfl (.cons (.tuple (.cons .unit .nil) innerLayout) (.cons .unit .nil)) outerLayout rfl)
  exact ⟨0,.child (index := 0) first (.tuple rfl (.cons .unit .nil) innerLayout rfl)⟩

private theorem destinationTyped (program : Language.Program) : AddressType program world destination .unit := by
  have base : AddressOffset program world ⟨0,0,[]⟩ outerType 0 := .root (root := root) rfl rfl
  exact ⟨0,.child (index := 1) base (.tuple rfl (.cons (.tuple (.cons .unit .nil) innerLayout) (.cons .unit .nil)) outerLayout rfl)⟩

private theorem referenceTyped (program : Kernel.Program) : Typing.ValueTyped program world referenceValue :=
  .reference (loan := loan) rfl rfl rfl rfl (sourceTyped program.declarations)

private theorem rootsTyped (program : Kernel.Program) :
    ∀ id resident value, world.roots.get id = some resident → resident.live = true → resident.value = some value →
      Typing.ValueTyped program world value ∧ value.type = resident.type := by
  intro id resident value found _ contents
  have member := Table.mem_of_get found
  simp [world] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have same : value = outer := by simpa [root] using contents.symm
    subst value
    refine ⟨.aggregate (Or.inl ⟨rfl,rfl,rfl⟩) (.resident ?_ rfl (.hole .nil)),rfl⟩
    exact .aggregate (Or.inl ⟨rfl,rfl,rfl⟩) (.resident .unit rfl .nil)
  · have same : value = referenceValue := by simpa [handleRoot] using contents.symm
    subst value
    exact ⟨referenceTyped program,rfl⟩

private theorem occupants {address value} (resident : world.Resident address value) :
    (address = ⟨0,0,[]⟩ ∧ value = outer) ∨ (address = ⟨0,0,[0]⟩ ∧ value = inner) ∨
    (address = source ∧ value = unitValue) ∨ (address = handle ∧ value = referenceValue) := by
  rcases address with ⟨id,generation,path⟩
  rcases resident with ⟨resident,whole,found,_,generations,contents,inside⟩
  have member := Table.mem_of_get found
  simp [world] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have wholeEq : whole = outer := by simpa [root] using contents.symm
    have generationEq : generation = 0 := generations
    subst whole generation
    have located := ResidentAt.iff_atPath.mp inside
    cases path with
    | nil =>
        have same : value = outer := Option.some.inj located.symm
        exact Or.inl ⟨rfl,same⟩
    | cons index path =>
        cases index with
        | zero =>
            have innerLocated : inner.atPath path = some value := located
            cases path with
            | nil => exact Or.inr (Or.inl ⟨rfl,Option.some.inj innerLocated.symm⟩)
            | cons index path =>
                cases index with
                | zero =>
                    have unitLocated : unitValue.atPath path = some value := innerLocated
                    have unitResident := ResidentAt.iff_atPath.mpr unitLocated
                    obtain ⟨rfl,rfl⟩ := leaf rfl unitResident
                    exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))
                | succ index => simp [Value.atPath,inner,Value.fields] at innerLocated
        | succ index =>
            cases index <;> simp [Value.atPath,outer,Value.fields] at located
  · have wholeEq : whole = referenceValue := by simpa [handleRoot] using contents.symm
    have generationEq : generation = 0 := generations
    subst whole generation
    obtain ⟨rfl,rfl⟩ := leaf rfl inside
    exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))

private theorem rootCases {id resident} (found : world.roots.get id = some resident) :
    (id = 0 ∧ resident = root) ∨ (id = 2 ∧ resident = handleRoot) := by
  have member := Table.mem_of_get found
  simpa [world] using member

private theorem worldValid : world.WellFormed := by
  refine ⟨by simp [world,Table.Unique],by simp [world,Table.Unique],by simp [world,PreservationChecks.world,Table.Unique],
    by decide,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro id available found
    simp [world,PreservationChecks.world,Table.get] at found
  · intro address value pack resident head
    rcases occupants resident with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases head
  · intro address value resident
    rcases occupants resident with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  · intro a b left right first second same
    rcases occupants first with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases occupants second with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> first | rfl | cases same
  · intro id resident found
    rcases rootCases found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [world,PreservationChecks.world,root,sourceRoot,handleRoot,Layout.Valid,PowerOfTwo] <;>
      first | exact ⟨0,rfl⟩ | exact ⟨3,rfl⟩
  · intro region member
    simp [world,PreservationChecks.world] at member
    subst region
    decide
  · intro id resident found _
    rcases rootCases found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  · intro a b left right first second different _ _
    rcases rootCases first with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases rootCases second with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      first | exact False.elim (different rfl) | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
  · intro id resident found
    have member := Table.mem_of_get found
    simp [world] at member
    obtain ⟨rfl,rfl⟩ := member
    exact ⟨rfl,by decide,fun _ => ⟨by decide,by decide⟩⟩
  · intro address value id resident head
    rcases occupants resident with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · cases head
    · cases head
    · cases head
    · have same : id = 0 := by cases head; rfl
      subst id
      exact ⟨loan,rfl,rfl⟩
  · intro a b left right first second _ _ _ _
    have firstMember := Table.mem_of_get first
    have secondMember := Table.mem_of_get second
    simp [world] at firstMember secondMember
    obtain ⟨rfl,rfl⟩ := firstMember
    obtain ⟨rfl,rfl⟩ := secondMember
    exact Or.inl .refl
  · intro id resident parent found selected
    have member := Table.mem_of_get found
    simp [world] at member
    obtain ⟨rfl,rfl⟩ := member
    cases selected
  · intro id resident found _
    have member := Table.mem_of_get found
    simp [world] at member
    obtain ⟨rfl,rfl⟩ := member
    exact Or.inl ⟨unitValue,rfl⟩
  · intro id resident guard found member
    have selected := Table.mem_of_get found
    simp [world] at selected
    obtain ⟨rfl,rfl⟩ := selected
    simp [loan] at member
  · intro id resident found
    have selected := Table.mem_of_get found
    simp [world] at selected
    obtain ⟨rfl,rfl⟩ := selected
    simp [loan,Loan.KindValid,LoanKind.Allows]

private theorem worldTyped (program : Kernel.Program)
    (pointer : program.declarations.input.target.pointerBits = 64) : Typing.WorldTyped program world := by
  refine ⟨worldValid,?_,?_,?_,?_⟩
  · intro address value resident
    exact World.stores_typed (rootsTyped program) (World.resident_iff_stores.mp resident)
  · intro id resident value found contents
    have live : resident.live = true := by
      rcases rootCases found with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rfl
    exact (rootsTyped program id resident value found live contents).2
  · intro id resident found
    rcases rootCases found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · intro region occurs
      cases occurs with
      | child member occurs =>
        simp [root,outerType,Term.children] at member
        rcases member with rfl | rfl
        · cases occurs with
          | child member occurs =>
            simp [innerType,Term.children] at member
            subst member
            cases occurs with
            | child member _ => simp [Term.children] at member
        · cases occurs with
          | child member _ => simp [Term.children] at member
    · intro region occurs
      cases occurs with
      | child member occurs =>
        simp [handleRoot,referenceType,Term.children] at member
        rcases member with rfl | rfl
        · cases occurs with
          | here => decide
          | child member _ => simp [Term.children] at member
        · cases occurs with
          | child member _ => simp [Term.children] at member
  · intro id resident found _
    rcases rootCases found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .tuple (.cons (.tuple (.cons .unit .nil) innerLayout) (.cons .unit .nil)) outerLayout
    · simpa [handleRoot,referenceType,pointer] using
        (LayoutOf.reference (program := program.declarations) (context := ⟨[],[],0,default,false,{}⟩)
          (mode := .unique) (region := .runtimeRegion 0) (referent := .unit))

/-- These are the actual two writes of the nested move, including a changed
parent two levels above the source. No post-state typing is supplied. -/
example (program : Kernel.Program) (valid : ProgramWellFormed program.declarations)
    (inventory : BodyInventory program) : Typing.ValueTyped program world movedValue := by
  have clear : world.write source none = some cleared := rfl
  have install : cleared.write destination (some unitValue) = some moved := rfl
  obtain ⟨offset,located⟩ := destinationTyped program.declarations
  have outside : ¬ source.ProperPrefix destination := by simp [Address.ProperPrefix,Address.Prefix,source,destination]
  have framed := (World.write_address_offsets clear outside).mp located
  have roots := World.write_typed_roots valid inventory (World.clear_typed_roots (rootsTyped program) clear) framed install
    (fun value equal => by cases Option.some.inj equal; exact ⟨.unit,rfl⟩)
  exact (roots 0 { root with value := some movedValue } movedValue rfl rfl rfl).1

/-- Replacing the nested tuple with unit is not a type-preserving edit, even
though both have zero-sized layouts in this fixture. -/
example (program : Kernel.Program) : ¬ Typing.ValueTyped program world (outer.withFields [some unitValue,none]) := by
  intro typed
  cases typed with
  | aggregate constructed fields =>
      rcases constructed with ⟨same,_,_⟩ | ⟨_,_,_,_,same,_⟩ | ⟨_,_,_,_,_,same,_⟩
      · have typesEq := Term.tuple.inj same
        cases typesEq
        cases fields with
        | resident _ impossible _ => cases impossible
      · cases same
      · cases same

private theorem move (program : RuntimeProgram) : Transfers program world (.loan 0) source destination moved := by
  refine .move (before := world) (source := source) (value := unitValue) (cleared := cleared) rfl initialized (unitReady program world _) ?_
    ⟨root,rfl,Or.inr ⟨[],1,outer,rfl,rfl,outer,rfl,rfl⟩⟩
    (by simp [Address.Overlaps,source,destination]) (destinationTyped program.declarations) rfl rfl
  refine ⟨⟨root,rfl⟩,loan,rfl,rfl,rfl,rfl,⟨[],rfl⟩,(fun _ => rfl),?_,?_,?_⟩
  · intro other resident found _ different
    have member := Table.mem_of_get found
    simp [world] at member
    exact False.elim (different member.1)
  · simp [loan]
  · intro other resident found _ member
    have selected := Table.mem_of_get found
    simp [world] at selected
    obtain ⟨rfl,rfl⟩ := selected
    simp [loan] at member

private theorem restore (program : RuntimeProgram) : Transfers program moved .owner destination source world := by
  have sourceOutside : ¬ source.ProperPrefix source := by rintro ⟨_,length⟩; exact Nat.lt_irrefl _ length
  have destinationOutside : ¬ destination.ProperPrefix source := by simp [Address.ProperPrefix,Address.Prefix,source,destination]
  refine .move (before := moved) (source := destination) (value := unitValue) (cleared := cleared) rfl initialized (unitReady program moved _) ?_
    ⟨{ root with value := some movedValue },rfl,Or.inr ⟨[0],0,movedValue,rfl,rfl,innerHole,rfl,rfl⟩⟩
    (by simp [Address.Overlaps,source,destination])
    (((move program).address_types sourceOutside destinationOutside).mp (sourceTyped program.declarations)) rfl rfl
  refine ⟨⟨{ root with value := some movedValue },rfl⟩,?_⟩
  intro id resident found _ overlap
  have member := Table.mem_of_get found
  simp [moved,world] at member
  obtain ⟨rfl,rfl⟩ := member
  simp [Address.Overlaps,source,destination,loan] at overlap

example (program : Kernel.Program) (valid : ProgramWellFormed program.declarations)
    (inventory : BodyInventory program) (pointer : program.declarations.input.target.pointerBits = 64) :
    Typing.WorldTyped program moved ∧ Typing.WorldTyped program world := by
  have movedTyped := (move program.toRuntimeProgram).worldTyped valid inventory (worldTyped program pointer)
  exact ⟨movedTyped,(restore program.toRuntimeProgram).worldTyped valid inventory movedTyped⟩

example (program : RuntimeProgram) : moved.WellFormed := (move program).wellFormed worldValid

/-- Both endpoints are fields of one root; the source lies two levels deep.
Its live unique handle survives the hole and the restoring owner transfer. -/
example (program : Kernel.Program) (host : Foreign.Model) (next : Task) :
    Typing.ValueTyped program world referenceValue ∧ Typing.ValueTyped program moved referenceValue ∧
    moved.Stores handle referenceValue ∧ moved.Vacant source ∧
    Run program host
      { world := world, task := .transfer source (.loan 0) destination (.transfer destination .owner source next) }
      [.move source destination,.move destination source] { world := world, task := next } := by
  refine ⟨referenceTyped program,?_,rfl,?_,?_⟩
  · exact (move program.toRuntimeProgram).reference_typed (loan := loan) rfl
      (by rintro ⟨_,length⟩; exact Nat.lt_irrefl _ length)
      (by simp [Address.ProperPrefix,Address.Prefix,loan,source,destination]) (referenceTyped program)
  · exact ⟨{ root with value := some movedValue },rfl,Or.inr ⟨[0],0,movedValue,rfl,rfl,innerHole,rfl,rfl⟩⟩
  · exact .visible (Or.inl (.transfer rfl (move _))) (.visible (Or.inl (.transfer rfl (restore _))) .refl)

/-- A proper-ancestor clear really destroys the child's resident; the frame
law deliberately cannot be applied there. -/
example : (outer.replace [0] none).bind (fun value => value.atPath [0,0]) = none ∧
    (⟨0,0,[0]⟩ : Address).ProperPrefix source := by
  exact ⟨rfl,⟨rfl,rfl,[0],rfl⟩,by decide⟩

private def widened : Loan := ⟨1,some 0,⟨0,0,[]⟩,.unique,0,true,.restoring,[],false,none⟩
private def forged : World := { world with loans := [(0,loan),(1,widened)], nextLoan := 2 }

/-- The permission rule alone really does trust the parent graph: this forged
child authorizes consumption of its parent's proper storage ancestor. The
strengthened authoritative world invariant rejects the graph itself. -/
example : Permitted forged (.loan 1) .owned ⟨0,0,[]⟩ ∧ ¬ forged.WellFormed := by
  constructor
  · refine ⟨⟨root,rfl⟩,widened,rfl,rfl,rfl,rfl,⟨[],rfl⟩,(fun _ => rfl),?_,?_,?_⟩
    · intro other resident found _ different _ _
      have member := Table.mem_of_get found
      simp [forged] at member
      rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact .parent (loan := widened) rfl rfl .refl
      · exact False.elim (different rfl)
    · simp [widened]
    · intro other resident found _ member
      have selected := Table.mem_of_get found
      simp [forged] at selected
      rcases selected with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [loan,widened] at member
  · intro valid
    obtain ⟨ancestor,found,_,included,_⟩ := World.loanParents valid 1 widened 0 rfl rfl
    have same : ancestor = loan := Option.some.inj (found.symm.trans (show forged.loans.get 0 = some loan from rfl))
    subst ancestor
    have impossible := included.length_le
    contradiction

private def missingAncestor : World := { world with roots := world.roots.set 0 { root with value := none } }

example : ¬ missingAncestor.WellFormed := by
  intro valid
  have located := World.liveLoanLocations valid 0 loan rfl rfl
  have vacant : missingAncestor.Vacant ⟨0,0,[]⟩ := ⟨{ root with value := none },rfl,Or.inl ⟨rfl,rfl⟩⟩
  exact vacant.no_located_descendant located ⟨⟨rfl,rfl,[0,0],rfl⟩,by decide⟩

end Nested

end Glorious.Language.PreservationChecks
