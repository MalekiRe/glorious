import GloriousLanguage.StorageFraming

/-! Shared permission and support projections for actual value handoffs.
Every reference view retains the authority that reached its handle. -/
namespace Glorious.Language

theorem World.root_bound {world : World} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) {id : Identity} {root : Root}
    (found : world.roots.get id = some root) : id < world.nextRoot :=
  (valid.2.2.2.2.2.2.2.2.1 id root found).1

theorem World.live_loan_root_bound {world : World} {id : Identity} {loan : Loan} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound)
    (found : world.loans.get id = some loan) (live : loan.live = true) : loan.referent.root < world.nextRoot := by
  have selected := ((valid.2.2.2.2.2.2.2.2.2.2.2.2.1 id loan found).2.2 live).2
  obtain ⟨root,present⟩ := Option.isSome_iff_exists.mp selected
  exact World.root_bound valid (World.root_found present).1


theorem LoanPermission.weaken {world : World} {identity : Identity}
    {available requested : Access} {address : Address}
    (permitted : LoanPermission world identity available address)
    (weaker : requested ≠ .shared → available ≠ .shared) :
    LoanPermission world identity requested address := by
  obtain ⟨loan,found,live,root,generation,path,mode,exclusion,guards,dependent⟩ := permitted
  refine ⟨loan,found,live,root,generation,path,fun nonshared => mode (weaker nonshared),?_,guards,?_⟩
  · intro other loan selected active different overlap conflict
    exact exclusion other loan selected active different overlap
      (conflict.elim (fun nonshared => Or.inl (weaker nonshared)) Or.inr)
  · intro other loan selected active guard
    by_cases shared : requested = .shared
    · exact shared
    · exact False.elim (weaker shared (dependent other loan selected active guard))

theorem Permitted.weaken {world : World} {authority : Authority}
    {available requested : Access} {address : Address}
    (permitted : Permitted world authority available address)
    (weaker : requested ≠ .shared → available ≠ .shared) :
    Permitted world authority requested address := by
  induction authority with
  | owner =>
      refine ⟨permitted.1,?_⟩
      intro id loan found live overlap conflict
      exact permitted.2 id loan found live overlap
        (conflict.elim (fun nonshared => Or.inl (weaker nonshared)) Or.inr)
  | loan id => exact ⟨permitted.1,permitted.2.weaken weaker⟩
  | shared backing ih =>
      refine ⟨permitted.1,?_,ih permitted.2.2⟩
      by_cases shared : requested = .shared
      · exact shared
      · exact False.elim (weaker shared permitted.2.1)
  | guarded backing carrier ih =>
      obtain ⟨loan,found,guard⟩ := permitted.2.2
      exact ⟨permitted.1,ih permitted.2.1,loan,found,guard.weaken weaker⟩

theorem Permitted.root {world : World} {authority : Authority} {access : Access} {address : Address}
    (permitted : Permitted world authority access address) : ∃ root, world.root address = some root := by
  cases authority <;> exact permitted.1

theorem Permitted.lend_shared {world : World} {authority : Authority}
    {access : Access} {address : Address} (permitted : Permitted world authority access address) :
    Permitted world (authority.lend access) .shared address := by
  have shared := permitted.weaken (requested := .shared) (fun nonshared => False.elim (nonshared rfl))
  unfold Authority.lend
  split
  · exact ⟨shared.root,rfl,shared⟩
  · exact shared

/-- Lending at the requested access does not change that access permission. -/
theorem Permitted.lend_iff {world : World} {authority : Authority} {access : Access} {address : Address} :
    Permitted world (authority.lend access) access address ↔ Permitted world authority access address := by
  unfold Authority.lend
  split
  · rename_i shared
    exact ⟨fun held => held.2.2,fun held => ⟨held.root,shared,held⟩⟩
  · rfl

/-- Guarded access requires the backing permission and exactly the explicit
carrier permissions, never the carriers' inherited dependency permissions. -/
theorem Permitted.guarded_fold_iff {world : World} {authority : Authority} {access : Access}
    {address : Address} (carriers : List Identity) :
    Permitted world (carriers.foldr (fun carrier backing => Authority.guarded backing carrier) authority) access address ↔
      Permitted world authority access address ∧
      ∀ carrier ∈ carriers, ∃ loan, world.loans.get carrier = some loan ∧ LoanPermission world carrier access loan.referent := by
  induction carriers with
  | nil => simp
  | cons carrier rest ih =>
    constructor
    · intro held
      obtain ⟨backing,carriers⟩ := ih.mp held.2.1
      refine ⟨backing,?_⟩
      intro identity member
      rcases List.mem_cons.mp member with rfl | member
      · exact held.2.2
      · exact carriers identity member
    · rintro ⟨backing,carriers⟩
      have held := ih.mpr ⟨backing,fun identity member => carriers identity (List.mem_cons_of_mem _ member)⟩
      exact ⟨held.root,held,carriers carrier List.mem_cons_self⟩

/-- The complete dereference permission contract. Inherited guards remain
checked for liveness by each LoanPermission; they are not requested again as
independent unique access after their dependent loan has frozen them. -/
theorem Permitted.referenceView_iff {world : World} {authority : Authority} {identity : Identity}
    {access : Access} {address : Address} :
    Permitted world (authority.referenceView identity access) access address ↔
      Permitted world (.loan identity) access address ∧
      ∀ carrier ∈ authority.carriers, ∃ loan, world.loans.get carrier = some loan ∧
        LoanPermission world carrier access loan.referent := by
  unfold Authority.referenceView Authority.throughReference
  rw [Permitted.lend_iff]
  exact Permitted.guarded_fold_iff _

theorem Permitted.resourceView_iff {world : World} {authority : Authority} {binding : StorageBinding}
    {incoming : Access} :
    Permitted world (authority.resourceView binding incoming) (ResourceAccess incoming binding) binding.address ↔
      Permitted world binding.authority (ResourceAccess incoming binding) binding.address ∧
      ∀ carrier ∈ authority.carriers, ∃ loan, world.loans.get carrier = some loan ∧
        LoanPermission world carrier (ResourceAccess incoming binding) loan.referent := by
  unfold Authority.resourceView
  rw [Permitted.lend_iff]
  exact Permitted.guarded_fold_iff _


theorem Authority.referenceView_lend (authority : Authority)
    (identity : Identity) (incoming requested : Access) :
    (authority.lend incoming).referenceView identity requested =
      authority.referenceView identity requested := by
  unfold Authority.lend
  split <;> rfl

theorem ReferenceView.of_permitted {world : World} {handle : Address}
    {authority : Authority} {incoming : Access}
    (permitted : Permitted world authority incoming handle) (identity : Identity) (mode : Mutability) :
    ReferenceView world handle (authority.lend incoming) identity mode
      (authority.referenceView identity (ReferenceAccess incoming mode))
      (ReferenceAccess incoming mode) := by
  cases mode with
  | shared =>
      refine Or.inl ⟨rfl,?_,?_⟩
      · simp only [ReferenceAccess,or_true,ite_true,Authority.referenceView_lend]
      · simp only [ReferenceAccess,or_true,ite_true]
  | unique =>
      by_cases shared : incoming = .shared
      · subst incoming
        refine Or.inr (Or.inr ⟨rfl,?_,?_,?_⟩)
        · intro unique
          exact Access.noConfusion (shared_authority_cannot_strengthen (by simpa only [Authority.lend,ite_true] using unique))
        · simp only [ReferenceAccess,true_or,ite_true,Authority.referenceView_lend]
        · simp only [ReferenceAccess,true_or,ite_true]
      · refine Or.inr (Or.inl ⟨rfl,?_,?_,?_⟩)
        · simpa only [Authority.lend,shared,ite_false] using
            permitted.weaken (requested := .unique) (fun _ => shared)
        · simp [ReferenceAccess,shared,Authority.referenceView_lend]
        · simp [ReferenceAccess,shared]

private theorem Address.overlaps_of_child {address other : Address} {index : Nat}
    (overlap : (address.child index).Overlaps other) : address.Overlaps other := by
  obtain ⟨root,generation,paths⟩ := overlap
  refine ⟨root,generation,?_⟩
  rcases paths with ⟨suffix,child⟩ | ⟨suffix,otherPath⟩
  · have initial : address.fields <+: (address.child index).fields :=
      List.prefix_iff_exists_eq_append.mpr ⟨[index],rfl⟩
    have otherPrefix : other.fields <+: (address.child index).fields :=
      List.prefix_iff_exists_eq_append.mpr ⟨suffix,child⟩
    rcases List.prefix_or_prefix_of_prefix initial otherPrefix with included | included
    · exact Or.inr (List.prefix_iff_exists_eq_append.mp included)
    · exact Or.inl (List.prefix_iff_exists_eq_append.mp included)
  · exact Or.inr ⟨[index] ++ suffix,by simpa only [Address.child,List.append_assoc] using otherPath⟩

theorem Permitted.child {world : World} {authority : Authority} {access : Access}
    {address : Address} (permitted : Permitted world authority access address) (index : Nat) :
    Permitted world authority access (address.child index) := by
  induction authority with
  | owner =>
      exact ⟨permitted.1,fun id loan found live overlap =>
        permitted.2 id loan found live (Address.overlaps_of_child overlap)⟩
  | loan id =>
      obtain ⟨loan,found,live,root,generation,⟨suffix,path⟩,mode,exclusion,guards,dependent⟩ := permitted.2
      refine ⟨permitted.1,loan,found,live,root,generation,⟨suffix ++ [index],?_⟩,mode,?_,guards,dependent⟩
      · simp only [Address.child,path,List.append_assoc]
      · intro other loan selected active different overlap conflict
        exact exclusion other loan selected active different (Address.overlaps_of_child overlap) conflict
  | shared backing ih => exact ⟨permitted.1,permitted.2.1,ih permitted.2.2⟩
  | guarded backing carrier ih => exact ⟨permitted.1,ih permitted.2.1,permitted.2.2⟩

theorem Value.LoansRestored.resident {program : RuntimeProgram} {world : World}
    {value child : Value} {path : List Nat} (restored : value.LoansRestored program world)
    (located : ResidentAt value path child) : child.LoansRestored program world :=
  fun identity current access reachable => restored identity current access (reachable.resident_prefix located)

theorem Value.LoansRestored.referent {program : RuntimeProgram} {world : World}
    {value target : Value} {authority current : Authority} {incoming access : Access}
    {identity : Identity} {loan : Loan}
    (restored : value.LoansRestored program world)
    (reachable : value.ReachableReference world authority incoming identity current access)
    (found : world.loans.get identity = some loan) (stored : world.Stores loan.referent target) :
    target.LoansRestored program world := by
  intro next nextAuthority nextAccess nested
  obtain ⟨base,requested,reached⟩ := reachable.rebase .owner .shared
  obtain ⟨view,access,nested⟩ := nested.rebase
    (base.referenceView identity (ReferenceAccess requested loan.mode)) (ReferenceAccess requested loan.mode)
  exact restored next view access (Value.ReachableReference.referent_prefix reached found stored nested)

theorem Value.SupportOutside.references {world : World} {value : Value} {source : Address}
    (outside : value.SupportOutside world source) : value.ReferencesOutside world source := by
  intro identity authority access reachable loan found
  obtain ⟨resident,reached,head⟩ := reachable
  exact outside loan.referent ⟨resident,authority,access,reached,Or.inl ⟨identity,loan,head,found,rfl⟩⟩

/-- Every observed reference or raw-resource support has an actual permitted
root. This follows the common graph, including supports that are raw holes. -/
theorem Value.ResourcesAccessible.support_root {program : RuntimeProgram} {world : World}
    {value : Value} {incoming : Access} (ready : value.ResourcesAccessible program world incoming)
    {address : Address} (supported : value.Support world address) :
    ∃ root, world.root address = some root := by
  obtain ⟨resident,authority,access,reached,support⟩ := supported
  rcases support with ⟨identity,loan,head,found,rfl⟩ | ⟨binding,member,rfl⟩
  · have reference : value.ReachableReference world .owner .shared identity authority access := ⟨resident,reached,head⟩
    obtain ⟨current,access,reference⟩ := reference.rebase .owner incoming
    obtain ⟨actual,selected,_,permitted⟩ := ready.references identity current access reference
    have same := Option.some.inj (found.symm.trans selected)
    subst actual
    exact permitted.root
  · obtain ⟨current,access,reached⟩ := reached.rebase .owner incoming
    exact (ready.2.2.2 resident current access reached binding member).root

/-- Fresh temporary roots are outside all support of every ready batch
value, not just the first transferred input. -/
theorem Value.ResourcesAccessible.supportOutside_fresh {program : RuntimeProgram} {world : World}
    {value : Value} {incoming : Access} (ready : value.ResourcesAccessible program world incoming)
    (well : world.WellFormed) {fresh : Address} (newRoot : world.nextRoot ≤ fresh.root) :
    value.SupportOutside world fresh := by
  intro address supported overlap
  obtain ⟨root,located⟩ := ready.support_root supported
  obtain ⟨_,_,_,_,_,_,_,_,bounds,_⟩ := well
  have below : address.root < world.nextRoot := (bounds address.root root (World.root_found located).1).1
  have same : fresh.root = address.root := overlap.1
  exact Nat.not_le_of_gt below (same ▸ newRoot)

end Glorious.Language
