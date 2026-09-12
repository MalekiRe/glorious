import GloriousLanguage.BufferAllocationPreservation

/-! A fresh buffer adds an independent owning root, not an alias of any
existing resource. These facts frame the actual resident support graph used
by reallocation; they do not assert equality of the changed loan tables. -/
namespace Glorious.Language.Memory

/-- The allocator returns the actual fresh owning authority. Its empty guard
list and fresh root exclude both competing access and incoming dependencies. -/
theorem AllocatesBuffer.owning_permission {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (access : Access) : Permitted after allocation.authority access allocation.address := by
  cases allocated
  refine ⟨by simp [World.root,Table.get_set],?_⟩
  refine ⟨_,Table.get_set _ _ _,rfl,rfl,rfl,⟨[],rfl⟩,(fun _ => rfl),?_,?_,?_⟩
  · intro id loan found live different overlap _
    have old := (Table.get_set_other _ _ _ _ different).symm.trans found
    obtain ⟨root,located⟩ := Option.isSome_iff_exists.mp
      ((valid.2.2.2.2.2.2.2.2.2.2.2.2.1 id loan old).2.2 live).2
    have bounded := World.root_bound valid (World.root_found located).1
    exact False.elim (Nat.ne_of_lt bounded overlap.1.symm)
  · simp
  · intro id loan found _ member
    by_cases same : id = before.nextLoan
    · subst id
      simp only [Table.get_set] at found
      cases found
      simp at member
    · have old := (Table.get_set_other _ _ _ _ same).symm.trans found
      obtain ⟨_,_,guardBound,_⟩ := World.loanGuards valid id loan before.nextLoan old member
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans guardBound (World.loanBounds valid old)))

theorem AllocatesBuffer.old_loan {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    {identity : Identity} {loan : Loan} (found : before.loans.get identity = some loan) :
    after.loans.get identity = some loan := by
  cases allocated
  exact (Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid found))).trans found

theorem AllocatesBuffer.guardsFramed {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after) :
    before.GuardsFramed after := by
  cases allocated
  intro identity
  by_cases same : identity = before.nextLoan
  · subst identity
    have absent : before.loans.get before.nextLoan = none := by
      cases found : before.loans.get before.nextLoan with
      | none => rfl
      | some loan => exact False.elim (Nat.lt_irrefl _ (World.loanBounds valid found))
    simp only [Table.get_set,absent,Option.map_none,Option.getD_none,Option.map_some,Option.getD_some]
  · simp only [Table.get_set_other _ _ _ _ same]

theorem AllocatesBuffer.ancestor_before {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    {ancestor descendant : Identity} (related : AncestorLoan after ancestor descendant) :
    AncestorLoan before ancestor descendant := by
  cases allocated
  induction related with
  | refl => exact .refl
  | @parent parent child loan selected link prior ih =>
      by_cases same : child = before.nextLoan
      · subst child
        simp only [Table.get_set] at selected
        cases selected
        cases link
      · exact .parent ((Table.get_set_other _ _ _ _ same).symm.trans selected) link ih

theorem AllocatesBuffer.loanPermission {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    {identity : Identity} {access : Access} {address : Address}
    (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (permission : LoanPermission before identity access address) : LoanPermission after identity access address := by
  have retained : ∀ {identity loan}, before.loans.get identity = some loan → after.loans.get identity = some loan :=
    fun found => allocated.old_loan valid found
  obtain ⟨loan,found,live,root,generation,path,mode,excluded,guards,dependent⟩ := permission
  obtain ⟨resident,located⟩ := Option.isSome_iff_exists.mp
    (((valid.2.2.2.2.2.2.2.2.2.2.2.2.1 identity loan found).2.2 live).2)
  have bound : address.root < before.nextRoot := root ▸ World.root_bound valid (World.root_found located).1
  cases allocated
  refine ⟨loan,retained found,live,root,generation,path,mode,?_,?_,?_⟩
  · intro other current selected active different overlap conflict
    by_cases same : other = before.nextLoan
    · subst other
      simp only [Table.get_set] at selected
      cases selected
      exact False.elim (Nat.ne_of_lt bound overlap.1)
    · have oldFound := (Table.get_set_other _ _ _ _ same).symm.trans selected
      exact (excluded other current oldFound active different overlap conflict).retained
        (fun key loan found => ⟨loan,retained found,rfl⟩)
  · intro guard member
    obtain ⟨carrier,selected,active⟩ := guards guard member
    exact ⟨carrier,retained selected,active⟩
  · intro other current selected active member
    by_cases same : other = before.nextLoan
    · subst other
      simp only [Table.get_set] at selected
      cases selected
      simp at member
    · exact dependent other current ((Table.get_set_other _ _ _ _ same).symm.trans selected) active member

theorem AllocatesBuffer.permitted {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    {authority : Authority} {access : Access} {address : Address}
    (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (permission : Permitted before authority access address) : Permitted after authority access address := by
  obtain ⟨root,selected⟩ := permission.root
  have located := allocated.root valid selected
  induction authority with
  | owner =>
      refine ⟨⟨root,located⟩,?_⟩
      have bound := World.root_bound valid (World.root_found selected).1
      cases allocated
      intro identity loan found live overlap conflict
      by_cases same : identity = before.nextLoan
      · subst identity
        simp only [Table.get_set] at found
        cases found
        exact Nat.ne_of_lt bound overlap.1
      · exact permission.2 identity loan ((Table.get_set_other _ _ _ _ same).symm.trans found) live overlap conflict
  | loan identity => exact ⟨⟨root,located⟩,allocated.loanPermission valid permission.2⟩
  | shared backing ih => exact ⟨⟨root,located⟩,permission.2.1,ih permission.2.2⟩
  | guarded backing carrier ih =>
      obtain ⟨loan,found,guard⟩ := permission.2.2
      exact ⟨⟨root,located⟩,ih permission.2.1,loan,allocated.old_loan valid found,allocated.loanPermission valid guard⟩

theorem AllocatesBuffer.custodied {program : Program} {before after : World}
    {custody recipient : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    {authority : Authority} (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (held : authority.Custodied before recipient) : authority.Custodied after recipient := by
  induction authority with
  | owner => trivial
  | loan identity =>
      obtain ⟨loan,found,kind⟩ := held
      exact ⟨loan,allocated.old_loan valid found,kind⟩
  | shared backing => exact held.transport (fun _ loan found => ⟨loan,allocated.old_loan valid found⟩)
  | guarded backing carrier ih => exact ih held

theorem AllocatesBuffer.allocationClaim {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    {authority : Authority} {address : Address} (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (claim : AllocationClaim before authority address) : AllocationClaim after authority address := by
  obtain ⟨identity,loan,root,ownerDomain,parent,found,live,kind,referent,whole,selected,home,latest⟩ := claim
  refine ⟨identity,loan,root,ownerDomain,parent,allocated.old_loan valid found,live,kind,referent,whole,
    allocated.root valid selected,home,?_⟩
  intro child successor selected active owning ancestry
  have prior := allocated.ancestor_before ancestry
  have oldChild : ∃ old, before.loans.get child = some old := by
    cases prior with
    | refl => exact ⟨loan,found⟩
    | parent selected => exact ⟨_,selected⟩
  obtain ⟨old,oldFound⟩ := oldChild
  have same := Option.some.inj ((allocated.old_loan valid oldFound).symm.trans selected)
  subst old
  exact latest child successor oldFound active owning prior

theorem AllocatesBuffer.heldBy {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    {binding : StorageBinding} {owner : Identity} (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (held : binding.HeldBy before owner) : binding.HeldBy after owner := by
  refine ⟨allocated.custodied valid held.1,?_⟩
  rcases held.2 with ⟨claim,writable⟩ | ⟨identity,loan,parent,found,live,kind,referent,shared⟩
  · exact Or.inl ⟨allocated.allocationClaim valid claim,writable⟩
  · exact Or.inr ⟨identity,loan,parent,allocated.old_loan valid found,live,kind,referent,shared⟩

theorem AllocatesBuffer.supportFramed {program : RuntimeProgram} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    {value : Value} {access : Access} (valid : before.WellFormed)
    (allocated : AllocatesBuffer program.declarations custody before domain element count base pointer allocation after)
    (ready : value.ResourcesAccessible program before access) : value.SupportFramed before after := by
  intro address supported
  obtain ⟨root,selected⟩ := ready.support_root supported
  have found := (World.root_found selected).1
  refine ⟨?_,?_⟩
  · change (after.root address >>= fun root => root.value >>= fun value => value.atPath address.fields) = _
    rw [allocated.root valid selected]
    change (root.value >>= fun value => value.atPath address.fields) = _
    simp only [World.read,selected]
    rfl
  · rw [allocated.roots valid found,found]

/-- The actual fresh owning-claim mutation preserves every existing ready
resident and all of its reachable reference/resource support. No post-world
permission or invariant is supplied by the caller. -/
theorem AllocatesBuffer.handoffReady {program : RuntimeProgram} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    {value : Value} {access : Access} {footprint : List Address} (valid : before.WellFormed)
    (allocated : AllocatesBuffer program.declarations custody before domain element count base pointer allocation after)
    (ready : value.HandoffReady program before access footprint) : value.HandoffReady program after access footprint := by
  have rows : value.ReferenceRowsFramed before after := by
    intro identity current access reached
    obtain ⟨loan,found,_⟩ := ready.1.2.1 identity current access reached
    exact congrArg (Option.map Loan.permissionState) ((allocated.old_loan valid found).trans found.symm)
  exact ready.frame_observed rows (allocated.guardsFramed valid) (allocated.supportFramed valid ready.1)
    (fun _ _ held => allocated.heldBy valid held) (fun _ _ _ permission => allocated.permitted valid permission)

end Glorious.Language.Memory
