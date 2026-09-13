import GloriousLanguage.AllocationPreservation
import GloriousLanguage.LoanPreservation

/-! Preservation through actual reference construction and its new parent
edge. Borrow permission and freshness establish the entire live loan graph;
no after-world well-formedness is an input contract. -/
namespace Glorious.Language

theorem World.write_leaf_origin {before after : World} {destination observed : Address}
    {owner : Identity} {type : Term} {head : ValueHead} {live : Bool} {value : Value}
    (written : before.write destination (some (.resident owner type head live [])) = some after)
    (resident : after.Resident observed value) :
    (observed = destination ∧ value = .resident owner type head live []) ∨
      ∃ original, before.Resident observed original ∧ value.shell = original.shell := by
  have stored := World.resident_iff_stores.mp resident
  by_cases included : destination.Prefix observed
  · obtain ⟨suffix,equal⟩ := Address.prefix_extension included
    have inside := World.write_read_inside written suffix
    rw [← equal,stored] at inside
    cases suffix with
    | nil => exact Or.inl ⟨by simpa using equal,by simpa [Value.atPath] using inside⟩
    | cons index suffix => simp [Value.atPath,Value.fields] at inside
  · have framed := World.write_read_shell written included
    rw [stored] at framed
    obtain ⟨original,found,same⟩ := Option.map_eq_some_iff.mp framed.symm
    exact Or.inr ⟨original,World.resident_iff_stores.mpr found,same.symm⟩

theorem FormsLoan.locations {purpose : LoanPurpose} {program : RuntimeProgram} {before after : World} {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  cases borrowed with
  | borrow _ _ _ _ _ _ _ _ _ _ written => exact World.write_locations written id

theorem FormsLoan.old_loan {purpose : LoanPurpose} {program : RuntimeProgram} {before after : World} {authority mode region referent destination}
    (valid : before.WellFormed) (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    {id : Identity} {loan : Loan} (found : before.loans.get id = some loan) : after.loans.get id = some loan := by
  cases borrowed
  simpa only [Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid found))] using found

theorem FormsLoan.resident_origin {purpose : LoanPurpose} {program : RuntimeProgram} {before after : World} {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    {observed : Address} {value : Value} (resident : after.Resident observed value) :
    (observed = destination ∧ value.owner = before.nextOwner ∧ value.head = .reference before.nextLoan ∧ value.fields = []) ∨
      ∃ original, before.Resident observed original ∧ value.shell = original.shell := by
  cases borrowed with
  | borrow _ _ _ _ _ _ _ _ _ _ written =>
      rcases World.write_leaf_origin written resident with ⟨rfl,rfl⟩ | origin
      · exact Or.inl ⟨rfl,rfl,rfl,rfl⟩
      · exact Or.inr origin

theorem FormsLoan.owner_unique {purpose : LoanPurpose} {program : RuntimeProgram} {before after : World} {authority mode region referent destination}
    (valid : before.WellFormed) (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    ∀ a b x y, after.Resident a x → after.Resident b y → x.owner = y.owner → a = b := by
  intro a b x y first second same
  rcases borrowed.resident_origin first with ⟨rfl,owner,_,_⟩ | ⟨oldFirst,oldA,shellA⟩
  · rcases borrowed.resident_origin second with ⟨rfl,_,_,_⟩ | ⟨oldSecond,oldB,shellB⟩
    · rfl
    · have oldOwner : y.owner = oldSecond.owner := by
        simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shellB
      have bound := World.owner_bound valid oldB
      rw [← oldOwner,← same,owner] at bound
      exact False.elim (Nat.lt_irrefl _ bound)
  · have oldOwnerA : x.owner = oldFirst.owner := by
      simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shellA
    rcases borrowed.resident_origin second with ⟨rfl,owner,_,_⟩ | ⟨oldSecond,oldB,shellB⟩
    · have bound := World.owner_bound valid oldA
      rw [← oldOwnerA,same,owner] at bound
      exact False.elim (Nat.lt_irrefl _ bound)
    · have oldOwnerB : y.owner = oldSecond.owner := by
        simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shellB
      exact valid.2.2.2.2.2.2.2.1 a b oldFirst oldSecond oldA oldB
        (oldOwnerA.symm.trans (same.trans oldOwnerB))

theorem FormsLoan.wellFormed {purpose : LoanPurpose} {program : RuntimeProgram} {before after : World} {authority mode region referent destination}
    (valid : before.WellFormed) (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    after.WellFormed := by
  have locations := borrowed.locations
  have ownersUnique := borrowed.owner_unique valid
  have located := borrowed.liveLoanLocations (World.liveLoanLocations valid)
  have oldLoan : ∀ {id loan}, before.loans.get id = some loan → after.loans.get id = some loan :=
    borrowed.old_loan valid
  have origin : ∀ {observed value}, after.Resident observed value →
      (observed = destination ∧ value.owner = before.nextOwner ∧ value.head = .reference before.nextLoan ∧ value.fields = []) ∨
        ∃ original, before.Resident observed original ∧ value.shell = original.shell := borrowed.resident_origin
  cases borrowed with
  | @borrow value middle parent stored referentType initialized regionLive addressable ready permitted vacant destinationType parentEq written =>
    have modeSame : (if (if mode = .shared then Access.shared else .unique) = .shared then Mutability.shared else .unique) = mode := by
      cases mode <;> decide
    have claimed := before.fresh_loan_wellFormedWithOrigins valid permitted (Or.inl ⟨_,stored⟩) regionLive purpose.kind none
      (by cases purpose <;> simp [LoanPurpose.kind,LoanKind.Allows])
    simp only [modeSame,← parentEq] at claimed
    have parents := World.loanParents claimed
    have guards := World.loanGuards claimed
    have kinds := World.loanKinds claimed
    have rest := World.write_rest written
    have proofEq := congrArg World.availability rest
    have regionsEq := congrArg World.liveRegions rest
    have rootBound := congrArg World.nextRoot rest
    have regionBound := congrArg World.nextRegion rest
    have proofBound := congrArg World.nextProof rest
    have rootsUnique := World.write_unique_roots valid.1 written
    rcases valid with ⟨_,loansUnique,proofsUnique,regionsUnique,proofs,packs,owners,_,roots,regions,bases,ranges,
      loans,references,_,_,_,_⟩
    refine ⟨rootsUnique,loansUnique.set _ _,?_,?_,?_,?_,?_,ownersUnique,?_,?_,?_,?_,?_,?_,?_,parents,located,guards,kinds⟩
    · simpa only [proofEq] using proofsUnique
    · simpa only [regionsEq] using regionsUnique
    · intro id available found
      have oldFound : before.availability.get id = some available := by simpa only [proofEq] using found
      obtain ⟨identity,bound,brand,active,recorded⟩ := proofs id available oldFound
      refine ⟨identity,by simpa only [proofBound] using bound,brand,?_,
        fun place member => (recorded place member).transport (fun _ loan found => ⟨loan,oldLoan found⟩)⟩
      intro live
      obtain ⟨region,reserved⟩ := active live
      refine ⟨by simpa only [regionsEq] using region,?_⟩
      intro place member
      obtain ⟨root,selected⟩ := Option.isSome_iff_exists.mp (reserved place member)
      obtain ⟨_,afterRoot,_⟩ := World.root_transport locations selected
      simp [afterRoot]
    · intro address value pack resident head
      rcases origin resident with ⟨_,_,fresh,_⟩ | ⟨original,oldResident,shell⟩
      · cases fresh.symm.trans head
      · have oldHead : original.head = .bindings pack := by
          have same : value.head = original.head := by
            simpa [Value.shell,Value.withFields,Value.head] using congrArg Value.head shell
          exact same.symm.trans head
        have arity : value.fields.length = original.fields.length := by
          simpa [Value.shell,Value.withFields,Value.fields] using congrArg (fun value => value.fields.length) shell
        obtain ⟨brand,region,length,distinct,facts⟩ := packs address original pack oldResident oldHead
        refine ⟨by simpa only [proofBound] using brand,by simpa only [regionsEq] using region,
          length.trans arity.symm,distinct,?_⟩
        intro fact member
        exact Nat.lt_succ_of_lt (facts fact member)
    · intro address value resident
      rcases origin resident with ⟨_,fresh,_,_⟩ | ⟨original,oldResident,shell⟩
      · simpa only [fresh] using Nat.lt_succ_self before.nextOwner
      · have same : value.owner = original.owner := by
          simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shell
        simpa only [same] using Nat.lt_succ_of_lt (owners address original oldResident)
    · intro id root found
      obtain ⟨original,oldFound,same⟩ := World.root_origin locations found
      rw [same]
      simpa only [rootBound,regionsEq] using roots id original oldFound
    · simpa only [regionsEq,regionBound] using regions
    · intro id root found live
      obtain ⟨original,oldFound,same⟩ := World.root_origin locations found
      have oldLive : original.live = true := by rw [same] at live; exact live
      rw [same]
      exact bases id original oldFound oldLive
    · intro a b left right leftFound rightFound different leftLive rightLive
      obtain ⟨oldLeft,oldFirst,leftEq⟩ := World.root_origin locations leftFound
      obtain ⟨oldRight,oldSecond,rightEq⟩ := World.root_origin locations rightFound
      have oldLeftLive : oldLeft.live = true := by rw [leftEq] at leftLive; exact leftLive
      have oldRightLive : oldRight.live = true := by rw [rightEq] at rightLive; exact rightLive
      rw [leftEq,rightEq]
      exact ranges a b oldLeft oldRight oldFirst oldSecond different oldLeftLive oldRightLive
    · intro id loan found
      by_cases fresh : id = before.nextLoan
      · subst id
        simp only [Table.get_set] at found
        cases found
        refine ⟨rfl,Nat.lt_succ_self _,?_⟩
        intro _
        refine ⟨by simpa only [regionsEq] using regionLive,?_⟩
        obtain ⟨root,selected,_⟩ := Option.bind_eq_some_iff.mp stored
        obtain ⟨_,afterRoot,_⟩ := World.root_transport locations selected
        simp [afterRoot]
      · have oldFound : before.loans.get id = some loan := by
          simpa only [Table.get_set_other _ _ _ _ fresh] using found
        obtain ⟨identity,bound,active⟩ := loans id loan oldFound
        refine ⟨identity,Nat.lt_succ_of_lt bound,?_⟩
        intro live
        obtain ⟨region,root⟩ := active live
        refine ⟨by simpa only [regionsEq] using region,?_⟩
        obtain ⟨_,selected⟩ := Option.isSome_iff_exists.mp root
        obtain ⟨_,afterRoot,_⟩ := World.root_transport locations selected
        simp [afterRoot]
    · intro address value id resident head
      rcases origin resident with ⟨_,_,fresh,_⟩ | ⟨original,oldResident,shell⟩
      · have same : before.nextLoan = id := ValueHead.reference.inj (fresh.symm.trans head)
        subst id
        exact ⟨_,Table.get_set _ _ _,rfl⟩
      · have same : value.head = original.head := by
          simpa [Value.shell,Value.withFields,Value.head] using congrArg Value.head shell
        obtain ⟨loan,found,live⟩ := references address original id oldResident (same.symm.trans head)
        exact ⟨loan,oldLoan found,live⟩
    · intro a b left right first second leftLive rightLive overlap unique
      have related := claimed.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a b left right
        first second leftLive rightLive overlap unique
      exact related.elim
        (fun ancestor => Or.inl (ancestor.retained (fun _ loan found => ⟨loan,found,rfl⟩)))
        (fun ancestor => Or.inr (ancestor.retained (fun _ loan found => ⟨loan,found,rfl⟩)))

theorem Typing.ValueTyped.borrow {purpose : LoanPurpose} {program : Kernel.Program} {before after : World}
    {authority mode region referent destination value}
    (valid : before.WellFormed)
    (borrowed : FormsLoan program.toRuntimeProgram purpose before authority mode region referent destination after)
    (typed : Typing.ValueTyped program before value) : Typing.ValueTyped program after value := by
  apply typed.transport ?_ ?_ (fun _ origin => origin.transport borrowed.locations)
  · intro id loan found active
    refine ⟨borrowed.old_loan valid found,?_⟩
    intro type located
    cases borrowed with
    | borrow _ _ _ _ _ _ _ vacant _ _ written =>
        exact ((World.write_address_types written (vacant.no_located_descendant
          (World.liveLoanLocations valid _ _ found active))).mp located).retained
            (fun _ selected => selected) (fun _ => rfl)
  · cases borrowed with
    | borrow _ _ _ _ _ _ _ _ _ _ written =>
        have same := congrArg World.availability (World.write_rest written)
        exact same

/-- Borrow construction types both the new handle and every changed enclosing
aggregate from the actual input address/layout derivation. In particular,
`Addressable` head classification alone is not a referent-location proof. -/
theorem FormsLoan.worldTyped {purpose : LoanPurpose} {program : Kernel.Program} {before after : World} {authority mode region referent destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (borrowed : FormsLoan program.toRuntimeProgram purpose before authority mode region referent destination after) :
    Typing.WorldTyped program after := by
  have well := borrowed.wellFormed typed.1
  have retained : ∀ value, Typing.ValueTyped program before value → Typing.ValueTyped program after value :=
    fun _ value => value.borrow typed.1 borrowed
  cases borrowed with
  | borrow stored referentType _ _ _ _ _ vacant destinationType _ written =>
    obtain ⟨offset,destinationType⟩ := destinationType
    have roots := World.write_typed_roots valid inventory
      (fun id root resident found live contents =>
        ⟨retained _ (typed.roots id root resident found live contents).1,
          (typed.roots id root resident found live contents).2⟩)
      destinationType written
      (fun resident same => by
        cases Option.some.inj same
        exact ⟨.reference (Table.get_set _ _ _) rfl rfl rfl
          (((World.write_address_types written (vacant.no_located_descendant (Or.inl ⟨_,stored⟩))).mp referentType).retained
            (fun _ selected => selected) (fun _ => rfl)),rfl⟩)
    have realized := typed.2.2.2.2.of_locations (World.write_locations written)
    refine ⟨well,?_,?_,?_,realized⟩
    · intro address value resident
      exact World.stores_typed roots (World.resident_iff_stores.mp resident)
    · intro id root value found contents
      by_cases live : root.live = true
      · exact (roots id root value found live contents).2
      · exact typed.2.2.1 id root value (World.write_dead_root written found live) contents
    · intro id root found
      obtain ⟨original,oldFound,same⟩ := World.root_origin (World.write_locations written) found
      have bound := congrArg World.nextRegion (World.write_rest written)
      rw [same]
      simpa only [bound] using typed.2.2.2.1 id original oldFound

namespace Execution

theorem Temporary.wellFormed {program : Kernel.Program} {context : Context} {type : Term}
    {before after : World} {address : Address} (valid : before.WellFormed)
    (temporary : Temporary program context type before address after) : after.WellFormed := by
  obtain ⟨_,allocated⟩ := temporary
  exact allocated.wellFormed valid

theorem Temporary.worldTyped {program : Kernel.Program} {context : Context} {type : Term}
    {before after : World} {address : Address} (typed : Typing.WorldTyped program before)
    (temporary : Temporary program context type before address after) : Typing.WorldTyped program after := by
  obtain ⟨_,allocated⟩ := temporary
  exact allocated.worldTyped typed

end Execution

end Glorious.Language
