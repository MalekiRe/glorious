import GloriousLanguage.Preservation

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
private def loan : Loan := ⟨0,none,source,.unique,0,true⟩
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
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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

private theorem referenceTyped (program : Kernel.Program) : Typing.ValueTyped program world referenceValue :=
  .reference (loan := loan) rfl rfl rfl rfl ⟨0,.root (root := sourceRoot) (id := 0) rfl rfl⟩

example (program : Kernel.Program) : Typing.WorldTyped program world := by
  refine ⟨worldValid,?_,?_⟩
  · intro address value resident
    rcases occupants resident with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .unit
    · exact referenceTyped program
  · intro id root value found stored
    rcases roots found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [sourceRoot,vacantRoot,handleRoot] at stored <;> subst value <;> rfl

private theorem move (program : Language.Program) : Transfers program world (.loan 0) source destination moved := by
  refine .move (value := unitValue) (cleared := cleared) rfl initialized ?_
    ⟨vacantRoot,rfl,Or.inl ⟨rfl,rfl⟩⟩ (by simp [source,destination,Address.Overlaps])
    ⟨0,.root (root := vacantRoot) (id := 1) rfl rfl⟩ rfl rfl
  refine ⟨⟨sourceRoot,rfl⟩,loan,rfl,rfl,rfl,rfl,⟨[],rfl⟩,(fun _ => rfl),?_⟩
  intro other resident found _ different
  have member := Table.mem_of_get found
  simp [world] at member
  exact False.elim (different member.1)

private theorem restore (program : Language.Program) : Transfers program moved .owner destination source world := by
  refine .move (value := unitValue) (cleared := restoreCleared) rfl initialized ?_
    ⟨vacantRoot,rfl,Or.inl ⟨rfl,rfl⟩⟩ (by simp [source,destination,Address.Overlaps])
    ⟨0,.root (root := vacantRoot) (id := 0) rfl rfl⟩ rfl rfl
  refine ⟨⟨sourceRoot,rfl⟩,?_⟩
  intro id resident found _ overlap
  have member := Table.mem_of_get found
  simp [moved,cleared,world] at member
  obtain ⟨rfl,rfl⟩ := member
  simp [source,destination,loan,Address.Overlaps] at overlap

/-- This state was excluded by the old reference-typing premise, which
required a resident at the referent. Reading and ending the loan still fail. -/
example (program : Kernel.Program) :
    Transfers program.declarations world (.loan 0) source destination moved ∧
    moved.Stores handle referenceValue ∧ Typing.ValueTyped program moved referenceValue ∧
    moved.Vacant source ∧ ¬ moved.Initialized source ∧
    (∀ after, ¬ EndsLoan moved 0 after) ∧ Transfers program.declarations moved .owner destination source world := by
  refine ⟨move _,rfl,(move program.declarations).reference_preserved worldValid (referenceTyped program),
    ⟨vacantRoot,rfl,Or.inl ⟨rfl,rfl⟩⟩,?_,?_,restore _⟩
  · rintro ⟨value,stored,_⟩
    cases stored
  · intro after
    exact hole_cannot_end (loan := loan) rfl (by rintro ⟨value,stored,_⟩; cases stored)

example (program : Kernel.Program) : moved.LoanParents ∧ moved.LiveLoanLocations ∧
    Typing.ValueTyped program moved referenceValue :=
  ⟨(move program.declarations).loanParents (World.loanParents worldValid),
    (move program.declarations).liveLoanLocations worldValid,
    (referenceTyped program).transfer worldValid (move program.declarations)⟩

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

example (program : Language.Program) (after : World) :
    ¬ Transfers program badWorld (.loan 0) source destination after := by
  intro transfer
  exact noUnitDestination program (transfer.destination_type (value := unitValue) rfl)

example (program : Language.Program) (after : World) :
    ¬ Copies program badWorld (.loan 0) source destination after := by
  intro copy
  exact noUnitDestination program (copy.destination_type (value := unitValue) rfl)

example (program : Language.Program) (after : World) :
    ¬ NewValue program badWorld destination .unit .unit [] after := by
  intro constructed
  exact noUnitDestination program constructed.destination_type

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
private def loan : Loan := ⟨0,none,source,.unique,0,true⟩
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

private theorem move (program : Language.Program) : Transfers program world (.loan 0) source destination moved := by
  refine .move (value := unitValue) (cleared := cleared) rfl initialized ?_
    ⟨root,rfl,Or.inr ⟨[],1,outer,rfl,rfl,outer,rfl,rfl⟩⟩
    (by simp [Address.Overlaps,source,destination]) (destinationTyped program) rfl rfl
  refine ⟨⟨root,rfl⟩,loan,rfl,rfl,rfl,rfl,⟨[],rfl⟩,(fun _ => rfl),?_⟩
  intro other resident found _ different
  have member := Table.mem_of_get found
  simp [world] at member
  exact False.elim (different member.1)

private theorem restore (program : Language.Program) : Transfers program moved .owner destination source world := by
  have sourceOutside : ¬ source.ProperPrefix source := by rintro ⟨_,length⟩; exact Nat.lt_irrefl _ length
  have destinationOutside : ¬ destination.ProperPrefix source := by simp [Address.ProperPrefix,Address.Prefix,source,destination]
  refine .move (value := unitValue) (cleared := cleared) rfl initialized ?_
    ⟨{ root with value := some movedValue },rfl,Or.inr ⟨[0],0,movedValue,rfl,rfl,innerHole,rfl,rfl⟩⟩
    (by simp [Address.Overlaps,source,destination])
    (((move program).address_types sourceOutside destinationOutside).mp (sourceTyped program)) rfl rfl
  refine ⟨⟨{ root with value := some movedValue },rfl⟩,?_⟩
  intro id resident found _ overlap
  have member := Table.mem_of_get found
  simp [moved,world] at member
  obtain ⟨rfl,rfl⟩ := member
  simp [Address.Overlaps,source,destination,loan] at overlap

/-- Both endpoints are fields of one root; the source lies two levels deep.
Its live unique handle survives the hole and the restoring owner transfer. -/
example (program : Kernel.Program) (host : Foreign.Model) (next : Task) :
    Typing.ValueTyped program world referenceValue ∧ Typing.ValueTyped program moved referenceValue ∧
    moved.Stores handle referenceValue ∧ moved.Vacant source ∧
    Run program host
      { world := world, task := .transfer source (.loan 0) destination (.transfer destination .owner source next) }
      [.move source destination,.move destination source] { world := world, task := next } := by
  refine ⟨referenceTyped program,?_,rfl,?_,?_⟩
  · exact (move program.declarations).reference_typed (loan := loan) rfl
      (by rintro ⟨_,length⟩; exact Nat.lt_irrefl _ length)
      (by simp [Address.ProperPrefix,Address.Prefix,loan,source,destination]) (referenceTyped program)
  · exact ⟨{ root with value := some movedValue },rfl,Or.inr ⟨[0],0,movedValue,rfl,rfl,innerHole,rfl,rfl⟩⟩
  · exact .visible (Or.inl (.transfer rfl (move _))) (.visible (Or.inl (.transfer rfl (restore _))) .refl)

/-- A proper-ancestor clear really destroys the child's resident; the frame
law deliberately cannot be applied there. -/
example : (outer.replace [0] none).bind (fun value => value.atPath [0,0]) = none ∧
    (⟨0,0,[0]⟩ : Address).ProperPrefix source := by
  exact ⟨rfl,⟨rfl,rfl,[0],rfl⟩,by decide⟩

private def widened : Loan := ⟨1,some 0,⟨0,0,[]⟩,.unique,0,true⟩
private def forged : World := { world with loans := [(0,loan),(1,widened)], nextLoan := 2 }

/-- The permission rule alone really does trust the parent graph: this forged
child authorizes consumption of its parent's proper storage ancestor. The
strengthened authoritative world invariant rejects the graph itself. -/
example : Permitted forged (.loan 1) .owned ⟨0,0,[]⟩ ∧ ¬ forged.WellFormed := by
  constructor
  · refine ⟨⟨root,rfl⟩,widened,rfl,rfl,rfl,rfl,⟨[],rfl⟩,(fun _ => rfl),?_⟩
    intro other resident found _ different _ _
    have member := Table.mem_of_get found
    simp [forged] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .parent (loan := widened) rfl rfl .refl
    · exact False.elim (different rfl)
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
