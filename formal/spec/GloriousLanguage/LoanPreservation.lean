import GloriousLanguage.AllocationFraming

/-! Actual raw claim creation and custody handoff preserve the one loan
structure and resident typing. Administrative changes retain the permission
projection of each real record, not an invented unchanged loan table. -/
namespace Glorious.Language

theorem Permitted.conflicting_parent {world : World} {authority : Authority} {access : Access} {address : Address}
    {id : Identity} {loan : Loan} (permitted : Permitted world authority access address)
    (found : world.loans.get id = some loan) (live : loan.live = true)
    (overlap : address.Overlaps loan.referent) (conflict : Conflict access loan.mode) :
    ∃ parent, authority.parentLoan = some parent ∧ AncestorLoan world id parent := by
  induction authority with
  | owner => exact False.elim (permitted.2 id loan found live overlap conflict)
  | loan parent =>
      refine ⟨parent,rfl,?_⟩
      by_cases same : id = parent
      · subst id; exact .refl
      · obtain ⟨_,_,_,_,_,_,_,exclusion,_,_⟩ := permitted.2
        exact exclusion id loan found live same overlap conflict
  | shared backing ih => exact ih permitted.2.2
  | guarded backing carrier ih => exact ih permitted.2.1

/-- A fresh conflicting child cannot become an ancestor of its old source
authority. This one identity-order argument serves source references and raw
storage claims, including retained records with changed administrative fields. -/
theorem Permitted.excludes_new_loan {before future : World} {authority : Authority}
    {available requested : Access} {address : Address} {identity : Identity} {loan : Loan}
    (valid : before.WellFormed) (futureValid : future.WellFormed)
    (permission : Permitted before authority available address)
    (found : future.loans.get identity = some loan) (live : loan.live = true)
    (fresh : before.nextLoan ≤ identity) (overlap : address.Overlaps loan.referent)
    (conflict : Conflict requested loan.mode) : ¬ Permitted future authority requested address := by
  intro allowed
  obtain ⟨parent,selected,ancestor⟩ := allowed.conflicting_parent found live overlap conflict
  obtain ⟨original,atParent,_,_,_⟩ := permission.parentLoan selected
  have bound := World.loanBounds valid atParent
  have ordered := ancestor.identity_le (World.loanParents futureValid)
  exact Nat.not_lt_of_ge (Nat.le_trans fresh ordered) bound

theorem LoanPermission.guard_live {world : World} {identity : Identity} {access : Access} {address : Address}
    {loan : Loan} (permission : LoanPermission world identity access address)
    (found : world.loans.get identity = some loan) :
    loan.live = true ∧ ∀ guard ∈ loan.guards, ∃ carrier, world.loans.get guard = some carrier ∧ carrier.live = true := by
  obtain ⟨current,selected,live,_,_,_,_,_,guards,_⟩ := permission
  have same := Option.some.inj (found.symm.trans selected)
  subst current
  exact ⟨live,guards⟩

theorem Permitted.guardLoans {world : World} {authority : Authority} {access : Access} {address : Address}
    (permission : Permitted world authority access address) :
    ∀ guard ∈ authority.guardLoans world, ∃ carrier, world.loans.get guard = some carrier ∧ carrier.live = true := by
  induction authority with
  | owner => intro guard member; simp [Authority.guardLoans] at member
  | loan identity =>
      obtain ⟨current,found,_⟩ := permission.2
      simpa only [Authority.guardLoans,found,Option.map_some,Option.getD_some] using
        (permission.2.guard_live found).2
  | shared backing ih => exact ih permission.2.2
  | guarded backing carrier ih =>
      obtain ⟨loan,found,guardPermission⟩ := permission.2.2
      have live := guardPermission.guard_live found
      intro guard member
      simp only [Authority.guardLoans,found,Option.map_some,Option.getD_some,List.mem_append,List.mem_cons] at member
      rcases member with (rfl | member) | member
      · exact ⟨loan,found,live.1⟩
      · exact live.2 guard member
      · exact ih permission.2.1 guard member

theorem AncestorLoan.transport_parents {before after : World} {ancestor descendant : Identity}
    (related : AncestorLoan before ancestor descendant)
    (retained : ∀ identity original, before.loans.get identity = some original →
      ∃ current, after.loans.get identity = some current ∧ current.parent = original.parent) :
    AncestorLoan after ancestor descendant := by
  induction related with
  | refl => exact .refl
  | parent selected link _ ih =>
      obtain ⟨current,found,same⟩ := retained _ _ selected
      exact .parent found (same.trans link) ih

theorem AncestorLoan.retained {before after : World} {ancestor descendant : Identity}
    (related : AncestorLoan before ancestor descendant)
    (retained : ∀ identity original, before.loans.get identity = some original →
      ∃ current, after.loans.get identity = some current ∧ current.permissionState = original.permissionState) :
    AncestorLoan after ancestor descendant := by
  exact related.transport_parents (fun identity original selected => by
    obtain ⟨current,found,same⟩ := retained identity original selected
    exact ⟨current,found,(Loan.permissionState_eq_iff.mp same).2.1⟩)

theorem LoanPermission.permissionState_transport {before after : World} {identity : Identity}
    {access : Access} {address : Address} (permission : LoanPermission before identity access address)
    (forward : ∀ key original, before.loans.get key = some original →
      ∃ current, after.loans.get key = some current ∧ current.permissionState = original.permissionState)
    (backward : ∀ key current, after.loans.get key = some current →
      ∃ original, before.loans.get key = some original ∧ current.permissionState = original.permissionState) :
    LoanPermission after identity access address := by
  obtain ⟨original,selected,live,root,generation,path,mode,excluded,guards,dependent⟩ := permission
  obtain ⟨current,found,same⟩ := forward identity original selected
  obtain ⟨_,_,referent,modeEq,_,liveEq,_,guardEq⟩ := Loan.permissionState_eq_iff.mp same
  refine ⟨current,found,liveEq.trans live,?_,?_,?_,fun unique => modeEq.trans (mode unique),?_,?_,?_⟩
  · exact (congrArg Address.root referent).trans root
  · exact (congrArg Address.generation referent).trans generation
  · simpa only [referent] using path
  · intro other loan atLoan active different overlap conflict
    obtain ⟨old,oldFound,shape⟩ := backward other loan atLoan
    obtain ⟨_,_,oldReferent,oldMode,_,oldLive,_,_⟩ := Loan.permissionState_eq_iff.mp shape
    exact (excluded other old oldFound (oldLive ▸ active) different
      (by simpa only [oldReferent] using overlap) (by simpa only [oldMode] using conflict)).retained forward
  · intro guard member
    obtain ⟨carrier,atGuard,active⟩ := guards guard (guardEq ▸ member)
    obtain ⟨currentGuard,guardFound,shape⟩ := forward guard carrier atGuard
    exact ⟨currentGuard,guardFound,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.2.1.trans active⟩
  · intro other loan atLoan active member
    obtain ⟨old,oldFound,shape⟩ := backward other loan atLoan
    obtain ⟨_,_,_,_,_,oldLive,_,oldGuards⟩ := Loan.permissionState_eq_iff.mp shape
    exact dependent other old oldFound (oldLive ▸ active) (oldGuards ▸ member)

/-- Custody and return-request changes do not alter a physical access. Both
directions inspect the actual rows, so this is not an equality claim about
administrative records whose state really changed. -/
theorem Permitted.permissionState_transport {before after : World} {authority : Authority}
    {access : Access} {address : Address} (permission : Permitted before authority access address)
    (roots : after.roots = before.roots)
    (forward : ∀ key original, before.loans.get key = some original →
      ∃ current, after.loans.get key = some current ∧ current.permissionState = original.permissionState)
    (backward : ∀ key current, after.loans.get key = some current →
      ∃ original, before.loans.get key = some original ∧ current.permissionState = original.permissionState) :
    Permitted after authority access address := by
  have root : ∃ resident, after.root address = some resident := by
    simpa only [World.root,roots] using permission.root
  induction authority with
  | owner =>
      refine ⟨root,?_⟩
      intro identity loan found live overlap conflict
      obtain ⟨original,selected,same⟩ := backward identity loan found
      obtain ⟨_,_,referent,mode,_,active,_,_⟩ := Loan.permissionState_eq_iff.mp same
      exact permission.2 identity original selected (active ▸ live)
        (by simpa only [referent] using overlap) (by simpa only [mode] using conflict)
  | loan identity => exact ⟨root,permission.2.permissionState_transport forward backward⟩
  | shared backing ih => exact ⟨root,permission.2.1,ih permission.2.2⟩
  | guarded backing carrier ih =>
      obtain ⟨loan,found,allowed⟩ := permission.2.2
      obtain ⟨current,selected,same⟩ := forward carrier loan found
      have referent := (Loan.permissionState_eq_iff.mp same).2.2.1
      exact ⟨root,ih permission.2.1,current,selected,referent ▸ allowed.permissionState_transport forward backward⟩

theorem Loan.KindValid.transport {original current : Loan} (valid : original.KindValid)
    (shape : current.permissionState = original.permissionState)
    (custody : original.custody.isSome = true → current.custody.isSome = true) : current.KindValid := by
  obtain ⟨_,_,_,mode,_,_,kind,_⟩ := Loan.permissionState_eq_iff.mp shape
  exact ⟨fun owning => mode.trans (valid.1 (kind ▸ owning)),
    fun raw => custody (valid.2 (by simpa only [kind] using raw))⟩

theorem World.loan_table_wellFormedWithOrigins {world : World} {loans : Table Loan} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) (unique : loans.Unique)
    (forward : ∀ identity original, world.loans.get identity = some original →
      ∃ current, loans.get identity = some current ∧ current.permissionState = original.permissionState)
    (backward : ∀ identity current, loans.get identity = some current →
      ∃ original, world.loans.get identity = some original ∧ current.permissionState = original.permissionState)
    (custody : ∀ identity original current, world.loans.get identity = some original → loans.get identity = some current →
      original.custody.isSome = true → current.custody.isSome = true) :
    World.WellFormedWithOrigins { world with loans := loans } originBound := by
  obtain ⟨rootsUnique,_,proofsUnique,regionsUnique,proofs,packs,owners,ownersUnique,roots,regions,bases,ranges,
    bounds,references,overlaps,parents,locations,guards,kinds⟩ := valid
  refine ⟨rootsUnique,unique,proofsUnique,regionsUnique,?_,packs,owners,ownersUnique,roots,regions,bases,ranges,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · intro identity available selected
    obtain ⟨same,bound,brand,active,recorded⟩ := proofs identity available selected
    exact ⟨same,bound,brand,active,fun place member => (recorded place member).transport
      (fun id loan found => by obtain ⟨current,selected,_⟩ := forward id loan found; exact ⟨current,selected⟩)⟩
  · intro identity current selected
    obtain ⟨original,found,same⟩ := backward identity current selected
    obtain ⟨idEq,_,referent,_,region,live,_,_⟩ := Loan.permissionState_eq_iff.mp same
    obtain ⟨id,bound,active⟩ := bounds identity original found
    exact ⟨id.trans idEq.symm,bound,fun alive => by
      have originalActive := active (live ▸ alive)
      simpa only [region,referent,World.root] using originalActive⟩
  · intro address value identity resident head
    obtain ⟨original,found,live⟩ := references address value identity resident head
    obtain ⟨current,selected,same⟩ := forward identity original found
    exact ⟨current,selected,(Loan.permissionState_eq_iff.mp same).2.2.2.2.2.1.trans live⟩
  · intro a b left right first second leftLive rightLive overlap uniqueMode
    obtain ⟨oldLeft,oldFirst,leftShape⟩ := backward a left first
    obtain ⟨oldRight,oldSecond,rightShape⟩ := backward b right second
    obtain ⟨_,_,leftReferent,leftMode,_,leftActive,_,_⟩ := Loan.permissionState_eq_iff.mp leftShape
    obtain ⟨_,_,rightReferent,rightMode,_,rightActive,_,_⟩ := Loan.permissionState_eq_iff.mp rightShape
    have ancestry := overlaps a b oldLeft oldRight oldFirst oldSecond (leftActive ▸ leftLive) (rightActive ▸ rightLive)
      (by simpa only [leftReferent,rightReferent] using overlap)
      (by simpa only [leftMode,rightMode] using uniqueMode)
    exact ancestry.elim (fun related => Or.inl (related.retained forward))
      (fun related => Or.inr (related.retained forward))
  · intro identity current parent selected link
    obtain ⟨original,found,same⟩ := backward identity current selected
    obtain ⟨_,parentEq,referent,mode,_,live,_,_⟩ := Loan.permissionState_eq_iff.mp same
    obtain ⟨ancestor,atParent,bound,included,parentMode,parentLive⟩ := parents identity original parent found (parentEq ▸ link)
    obtain ⟨currentParent,parentFound,parentShape⟩ := forward parent ancestor atParent
    obtain ⟨_,_,parentReferent,currentMode,_,currentLive,_,_⟩ := Loan.permissionState_eq_iff.mp parentShape
    exact ⟨currentParent,parentFound,bound,by simpa only [parentReferent,referent] using included,
      fun unique => currentMode.trans (parentMode (mode ▸ unique)),
      fun active => currentLive.trans (parentLive (live ▸ active))⟩
  · intro identity current selected live
    obtain ⟨original,found,same⟩ := backward identity current selected
    obtain ⟨_,_,referent,_,_,active,_,_⟩ := Loan.permissionState_eq_iff.mp same
    exact referent ▸ locations identity original found (active ▸ live)
  · intro identity current guard selected member
    obtain ⟨original,found,same⟩ := backward identity current selected
    obtain ⟨_,_,_,_,_,live,_,guardEq⟩ := Loan.permissionState_eq_iff.mp same
    obtain ⟨carrier,atGuard,bound,guardLive⟩ := guards identity original guard found (guardEq ▸ member)
    obtain ⟨currentGuard,guardFound,guardShape⟩ := forward guard carrier atGuard
    have active := (Loan.permissionState_eq_iff.mp guardShape).2.2.2.2.2.1
    exact ⟨currentGuard,guardFound,bound,fun alive => active.trans (guardLive (live ▸ alive))⟩
  · intro identity current selected
    obtain ⟨original,found,shape⟩ := backward identity current selected
    exact (kinds identity original found).transport shape (custody identity original current found selected)

theorem World.loan_table_worldTyped {program : Kernel.Program} {world : World} {loans : Table Loan}
    (typed : Typing.WorldTyped program world) (unique : loans.Unique)
    (forward : ∀ identity original, world.loans.get identity = some original →
      ∃ current, loans.get identity = some current ∧ current.permissionState = original.permissionState)
    (backward : ∀ identity current, loans.get identity = some current →
      ∃ original, world.loans.get identity = some original ∧ current.permissionState = original.permissionState)
    (custody : ∀ identity original current, world.loans.get identity = some original → loans.get identity = some current →
      original.custody.isSome = true → current.custody.isSome = true) :
    Typing.WorldTyped program { world with loans := loans } := by
  refine ⟨world.loan_table_wellFormedWithOrigins typed.1 unique forward backward custody,?_,typed.2.2⟩
  intro address value resident
  have checked := typed.2.1 address value resident
  apply checked.transport_references (after := { world with loans := loans }) ?_ rfl
    (fun _ origin => origin.transport (fun _ => rfl))
  intro identity original selected active
  obtain ⟨current,found,same⟩ := forward identity original selected
  obtain ⟨_,_,referent,mode,region,live,_,_⟩ := Loan.permissionState_eq_iff.mp same
  exact ⟨current,found,live.trans active,mode,region,fun type located =>
    referent ▸ located.retained (fun _ found => found) (fun _ => rfl)⟩

theorem World.set_loan_retained {world : World} {identity : Identity} {original replacement : Loan}
    (selected : world.loans.get identity = some original)
    (shape : replacement.permissionState = original.permissionState) :
    ∀ key previous, world.loans.get key = some previous →
      ∃ current, (world.loans.set identity replacement).get key = some current ∧
        current.permissionState = previous.permissionState := by
  intro key previous found
  by_cases same : key = identity
  · subst key
    have equal := Option.some.inj (selected.symm.trans found)
    subst previous
    exact ⟨replacement,Table.get_set _ _ _,shape⟩
  · exact ⟨previous,by simpa only [Table.get_set_other _ _ _ _ same] using found,rfl⟩

theorem World.set_loan_reflected {world : World} {identity : Identity} {original replacement : Loan}
    (selected : world.loans.get identity = some original)
    (shape : replacement.permissionState = original.permissionState) :
    ∀ key current, (world.loans.set identity replacement).get key = some current →
      ∃ previous, world.loans.get key = some previous ∧ current.permissionState = previous.permissionState := by
  intro key current found
  by_cases same : key = identity
  · subst key
    simp only [Table.get_set] at found
    cases found
    exact ⟨original,selected,shape⟩
  · exact ⟨current,by simpa only [Table.get_set_other _ _ _ _ same] using found,rfl⟩

theorem World.set_loan_custody {world : World} {identity : Identity} {original replacement : Loan}
    (selected : world.loans.get identity = some original)
    (custody : original.custody.isSome = true → replacement.custody.isSome = true) :
    ∀ key previous current, world.loans.get key = some previous →
      (world.loans.set identity replacement).get key = some current →
      previous.custody.isSome = true → current.custody.isSome = true := by
  intro key previous current found changed present
  by_cases same : key = identity
  · subst key
    have oldSame := Option.some.inj (selected.symm.trans found)
    have newSame := Option.some.inj ((Table.get_set _ _ _).symm.trans changed)
    subst previous
    subst current
    exact custody present
  · have old := (Table.get_set_other _ _ _ _ same).symm.trans changed
    have same := Option.some.inj (found.symm.trans old)
    exact same ▸ present

theorem World.set_loan_wellFormedWithOrigins {world : World} {identity : Identity}
    {original replacement : Loan} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) (selected : world.loans.get identity = some original)
    (shape : replacement.permissionState = original.permissionState)
    (custody : original.custody.isSome = true → replacement.custody.isSome = true) :
    World.WellFormedWithOrigins { world with loans := world.loans.set identity replacement } originBound :=
  world.loan_table_wellFormedWithOrigins valid (valid.2.1.set _ _)
    (world.set_loan_retained selected shape) (world.set_loan_reflected selected shape) (world.set_loan_custody selected custody)

theorem World.set_loan_worldTyped {program : Kernel.Program} {world : World} {identity : Identity}
    {original replacement : Loan} (typed : Typing.WorldTyped program world)
    (selected : world.loans.get identity = some original)
    (shape : replacement.permissionState = original.permissionState)
    (custody : original.custody.isSome = true → replacement.custody.isSome = true) :
    Typing.WorldTyped program { world with loans := world.loans.set identity replacement } :=
  world.loan_table_worldTyped typed (typed.1.2.1.set _ _)
    (world.set_loan_retained selected shape) (world.set_loan_reflected selected shape) (world.set_loan_custody selected custody)

theorem World.map_loans_retained {world : World} {map : Loan → Loan}
    (shape : ∀ loan, (map loan).permissionState = loan.permissionState) :
    ∀ (identity : Identity) (original : Loan), world.loans.get identity = some original →
      ∃ current, Table.get (world.loans.map fun (key,loan) => (key,map loan)) identity = some current ∧
        current.permissionState = original.permissionState := by
  intro identity original found
  exact ⟨map original,(Table.get_map_values world.loans map identity).trans (by rw [found]; rfl),shape original⟩

theorem World.map_loans_reflected {world : World} {map : Loan → Loan}
    (shape : ∀ loan, (map loan).permissionState = loan.permissionState) :
    ∀ (identity : Identity) (current : Loan), Table.get (world.loans.map fun (key,loan) => (key,map loan)) identity = some current →
      ∃ original, world.loans.get identity = some original ∧ current.permissionState = original.permissionState := by
  intro identity current found
  obtain ⟨original,selected,rfl⟩ := Option.map_eq_some_iff.mp
    ((Table.get_map_values world.loans map identity).symm.trans found)
  exact ⟨original,selected,shape original⟩

theorem World.map_loans_custody {world : World} {map : Loan → Loan}
    (custody : ∀ loan, loan.custody.isSome = true → (map loan).custody.isSome = true) :
    ∀ identity original current, world.loans.get identity = some original →
      Table.get (world.loans.map fun (key,loan) => (key,map loan)) identity = some current →
      original.custody.isSome = true → current.custody.isSome = true := by
  intro identity original current found changed present
  have actual : Table.get (world.loans.map fun (key,loan) => (key,map loan)) identity = some (map original) :=
    (Table.get_map_values world.loans map identity).trans (by rw [found]; rfl)
  have same := Option.some.inj (actual.symm.trans changed)
  exact same ▸ custody original present

theorem World.map_loans_wellFormedWithOrigins {world : World} {originBound : Identity} {map : Loan → Loan}
    (valid : world.WellFormedWithOrigins originBound) (shape : ∀ loan, (map loan).permissionState = loan.permissionState)
    (custody : ∀ loan, loan.custody.isSome = true → (map loan).custody.isSome = true) :
    World.WellFormedWithOrigins { world with loans := world.loans.map fun (key,loan) => (key,map loan) } originBound := by
  exact world.loan_table_wellFormedWithOrigins valid
    (by simpa only [Table.Unique,List.map_map,Function.comp_def] using valid.2.1)
    (world.map_loans_retained shape) (world.map_loans_reflected shape) (world.map_loans_custody custody)

theorem World.map_loans_worldTyped {program : Kernel.Program} {world : World} {map : Loan → Loan}
    (typed : Typing.WorldTyped program world) (shape : ∀ loan, (map loan).permissionState = loan.permissionState)
    (custody : ∀ loan, loan.custody.isSome = true → (map loan).custody.isSome = true) :
    Typing.WorldTyped program { world with loans := world.loans.map fun (key,loan) => (key,map loan) } := by
  exact world.loan_table_worldTyped typed
    (by simpa only [Table.Unique,List.map_map,Function.comp_def] using typed.1.2.1)
    (world.map_loans_retained shape) (world.map_loans_reflected shape) (world.map_loans_custody custody)

theorem RelinquishesCustody.retained {before after : World} {custody : ClaimCustody}
    (relinquished : RelinquishesCustody before custody after)
    {identity : Identity} {loan : Loan} (selected : before.loans.get identity = some loan) :
    ∃ current, after.loans.get identity = some current ∧ current.permissionState = loan.permissionState := by
  cases relinquished
  exact before.map_loans_retained
    (map := fun loan => if loan.custody = some custody ∧ loan.kind = .storageBorrow then { loan with returnRequested := true } else loan)
    (fun loan => by split <;> rfl) identity loan selected

theorem RelinquishesCustody.reflected {before after : World} {custody : ClaimCustody}
    (relinquished : RelinquishesCustody before custody after)
    {identity : Identity} {loan : Loan} (selected : after.loans.get identity = some loan) :
    ∃ original, before.loans.get identity = some original ∧ loan.permissionState = original.permissionState := by
  cases relinquished
  exact before.map_loans_reflected
    (map := fun loan => if loan.custody = some custody ∧ loan.kind = .storageBorrow then { loan with returnRequested := true } else loan)
    (fun loan => by split <;> rfl) identity loan selected

theorem RelinquishesCustody.canEndStorage {before after : World} {custody : ClaimCustody} {id : Identity}
    (relinquished : RelinquishesCustody before custody after) (safe : CanEndStorage before id) : CanEndStorage after id := by
  refine ⟨?_,?_⟩
  · intro key loan found live
    obtain ⟨original,present,same⟩ := relinquished.reflected found
    have originalLive : original.live = true := (congrArg Loan.live same).symm.trans live
    have referent : loan.referent.root = original.referent.root := congrArg (fun loan => loan.referent.root) same
    rw [referent]
    exact safe.1 key original present originalLive
  · cases relinquished
    exact safe.2


theorem RelinquishesCustody.wellFormed {before after : World} {custody : ClaimCustody}
    (valid : before.WellFormed) (relinquished : RelinquishesCustody before custody after) : after.WellFormed := by
  cases relinquished
  exact before.map_loans_wellFormedWithOrigins valid
    (map := fun loan => if loan.custody = some custody ∧ loan.kind = .storageBorrow then { loan with returnRequested := true } else loan)
    (fun loan => by split <;> rfl) (fun loan present => by split <;> exact present)

theorem RelinquishesCustody.worldTyped {program : Kernel.Program} {before after : World} {custody : ClaimCustody}
    (typed : Typing.WorldTyped program before) (relinquished : RelinquishesCustody before custody after) :
    Typing.WorldTyped program after := by
  cases relinquished
  exact before.map_loans_worldTyped typed
    (map := fun loan => if loan.custody = some custody ∧ loan.kind = .storageBorrow then { loan with returnRequested := true } else loan)
    (fun loan => by split <;> rfl) (fun loan present => by split <;> exact present)

theorem RelinquishesCustody.permitted {before after : World} {custody : ClaimCustody}
    {authority : Authority} {access : Access} {address : Address}
    (relinquished : RelinquishesCustody before custody after) (permission : Permitted before authority access address) :
    Permitted after authority access address :=
  permission.permissionState_transport (by cases relinquished; rfl)
    (fun _ _ => relinquished.retained) (fun _ _ => relinquished.reflected)

/-- The reflected direction: a permission in the relinquished world was already
present. Custody administration and the return request move with the loan, never
the loan's permission geometry. -/
theorem RelinquishesCustody.permitted_reflected {before after : World} {custody : ClaimCustody}
    {authority : Authority} {access : Access} {address : Address}
    (relinquished : RelinquishesCustody before custody after) (permission : Permitted after authority access address) :
    Permitted before authority access address :=
  permission.permissionState_transport (by cases relinquished; rfl)
    (fun _ _ found => by
      obtain ⟨witness,selected,shape⟩ := relinquished.reflected found
      exact ⟨witness,selected,shape.symm⟩)
    (fun _ _ found => by
      obtain ⟨witness,selected,shape⟩ := relinquished.retained found
      exact ⟨witness,selected,shape.symm⟩)

theorem RequestsStorageReturn.retained {before after : World} {requested : Identity}
    (request : RequestsStorageReturn before requested after)
    {identity : Identity} {loan : Loan} (selected : before.loans.get identity = some loan) :
    ∃ current, after.loans.get identity = some current ∧ current.permissionState = loan.permissionState := by
  cases request with
  | request found active kind =>
      rename_i original
      exact before.set_loan_retained (replacement := { original with returnRequested := true }) found rfl identity loan selected

theorem RequestsStorageReturn.reflected {before after : World} {requested : Identity}
    (request : RequestsStorageReturn before requested after)
    {identity : Identity} {loan : Loan} (selected : after.loans.get identity = some loan) :
    ∃ original, before.loans.get identity = some original ∧ loan.permissionState = original.permissionState := by
  cases request with
  | request found active kind =>
      rename_i original
      exact before.set_loan_reflected (replacement := { original with returnRequested := true }) found rfl identity loan selected

theorem RequestsStorageReturn.wellFormed {before after : World} {requested : Identity}
    (valid : before.WellFormed) (request : RequestsStorageReturn before requested after) : after.WellFormed := by
  cases request with
  | request found _ _ => exact before.set_loan_wellFormedWithOrigins valid found rfl (fun present => present)

theorem RequestsStorageReturn.worldTyped {program : Kernel.Program} {before after : World} {requested : Identity}
    (typed : Typing.WorldTyped program before) (request : RequestsStorageReturn before requested after) :
    Typing.WorldTyped program after := by
  cases request with
  | request found _ _ => exact before.set_loan_worldTyped typed found rfl (fun present => present)

theorem RequestsStorageReturn.permitted {before after : World} {requested : Identity}
    {authority : Authority} {access : Access} {address : Address}
    (request : RequestsStorageReturn before requested after) (permission : Permitted before authority access address) :
    Permitted after authority access address :=
  permission.permissionState_transport (by cases request; rfl)
    (fun _ _ => request.retained) (fun _ _ => request.reflected)

theorem TransfersAllocation.retained {recipient : ClaimCustody} {before after : World} {place : ResolvedPlace}
    (transferred : TransfersAllocation recipient before place after)
    {identity : Identity} {original : Loan} (selected : before.loans.get identity = some original) :
    ∃ current, after.loans.get identity = some current ∧ current.permissionState = original.permissionState := by
  cases transferred with
  | transfer authority claim found =>
      rename_i key loan
      exact before.set_loan_retained (replacement := { loan with custody := some recipient }) found rfl identity original selected

theorem TransfersStorageLoan.retained {recipient : ClaimCustody} {before after : World} {place : ResolvedPlace}
    (transferred : TransfersStorageLoan recipient before place after)
    {identity : Identity} {original : Loan} (selected : before.loans.get identity = some original) :
    ∃ current, after.loans.get identity = some current ∧ current.permissionState = original.permissionState := by
  cases transferred with
  | unique authority found live kind mode referent =>
      rename_i key loan
      exact before.set_loan_retained (replacement := { loan with custody := some recipient }) found rfl identity original selected
  | shared => exact ⟨original,selected,rfl⟩

theorem TransfersAllocation.worldTyped {program : Kernel.Program} {recipient : ClaimCustody}
    {before after : World} {place : ResolvedPlace} (typed : Typing.WorldTyped program before)
    (transferred : TransfersAllocation recipient before place after) : Typing.WorldTyped program after := by
  cases transferred with
  | transfer _ _ found => exact before.set_loan_worldTyped typed found rfl (fun _ => rfl)

theorem TransfersStorageLoan.worldTyped {program : Kernel.Program} {recipient : ClaimCustody}
    {before after : World} {place : ResolvedPlace} (typed : Typing.WorldTyped program before)
    (transferred : TransfersStorageLoan recipient before place after) : Typing.WorldTyped program after := by
  cases transferred with
  | unique _ found _ _ _ _ => exact before.set_loan_worldTyped typed found rfl (fun _ => rfl)
  | shared => exact typed

/-- Every fresh claim uses the pre-state permission's actual parent and
guards. Freshness retains old rows and orders every new dependency; no
post-state well-formedness or reconstructed authority is assumed. -/
theorem World.fresh_loan_wellFormedWithOrigins {world : World} {originBound : Identity}
    {authority : Authority} {access : Access} {address : Address} {region : Identity}
    (valid : world.WellFormedWithOrigins originBound)
    (permission : Permitted world authority access address) (located : world.Located address)
    (regionLive : region ∈ world.liveRegions) (kind : LoanKind) (custody : Option ClaimCustody)
    (kindAllowed : kind.Allows (if access = .shared then .shared else .unique) custody) :
    World.WellFormedWithOrigins
      { world with
        loans := world.loans.set world.nextLoan
          ⟨world.nextLoan,authority.parentLoan,address,
            if access = .shared then .shared else .unique,region,true,kind,
            authority.guardLoans world,false,custody⟩
        nextLoan := world.nextLoan+1 } originBound := by
  let fresh : Loan := ⟨world.nextLoan,authority.parentLoan,address,
    if access = .shared then .shared else .unique,region,true,kind,
    authority.guardLoans world,false,custody⟩
  let future : World := { world with
    loans := world.loans.set world.nextLoan fresh
    nextLoan := world.nextLoan+1 }
  change future.WellFormedWithOrigins originBound
  have retained : ∀ identity loan, world.loans.get identity = some loan →
      future.loans.get identity = some loan := by
    intro identity loan selected
    exact (Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid selected))).trans selected
  have ancestry : ∀ {a b}, AncestorLoan world a b → AncestorLoan future a b :=
    fun related => related.retained (fun identity loan selected => ⟨loan,retained identity loan selected,rfl⟩)
  have selected : future.loans.get world.nextLoan = some fresh := Table.get_set _ _ _
  have old : ∀ identity loan, identity ≠ world.nextLoan → future.loans.get identity = some loan →
      world.loans.get identity = some loan := by
    intro identity loan different found
    exact (Table.get_set_other _ _ _ _ different).symm.trans found
  obtain ⟨rootsUnique,loansUnique,proofsUnique,regionsUnique,proofs,packs,owners,ownersUnique,roots,regions,bases,ranges,
    bounds,references,overlaps,parents,locations,guards,kinds⟩ := valid
  refine ⟨rootsUnique,loansUnique.set _ _,proofsUnique,regionsUnique,?_,packs,owners,ownersUnique,roots,regions,bases,ranges,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · intro identity available found
    obtain ⟨same,bound,brand,active,recorded⟩ := proofs identity available found
    exact ⟨same,bound,brand,active,fun place member => (recorded place member).transport
      (fun identity loan found => ⟨loan,retained identity loan found⟩)⟩
  · intro identity loan found
    by_cases same : identity = world.nextLoan
    · subst identity
      have equal := Option.some.inj (selected.symm.trans found)
      subst loan
      exact ⟨rfl,Nat.lt_succ_self _,fun _ => ⟨regionLive,by
        obtain ⟨root,found⟩ := permission.root
        change (world.root address).isSome = true
        simp only [found,Option.isSome_some]⟩⟩
    · obtain ⟨identity,bound,active⟩ := bounds identity loan (old identity loan same found)
      exact ⟨identity,Nat.lt_succ_of_lt bound,active⟩
  · intro address value identity resident head
    obtain ⟨loan,found,live⟩ := references address value identity resident head
    exact ⟨loan,retained identity loan found,live⟩
  · intro a b left right first second leftLive rightLive overlap unique
    by_cases leftFresh : a = world.nextLoan
    · subst a
      have equal := Option.some.inj (selected.symm.trans first)
      subst left
      by_cases rightFresh : b = world.nextLoan
      · subst b; exact Or.inl .refl
      · have found := old b right rightFresh second
        have conflict : Conflict access right.mode := by
          rcases unique with unique | unique
          · exact Or.inl (by intro shared; simp [fresh,shared] at unique)
          · exact Or.inr unique
        obtain ⟨parent,link,related⟩ := permission.conflicting_parent found rightLive overlap conflict
        exact Or.inr (.parent selected link (ancestry related))
    · have oldLeft := old a left leftFresh first
      by_cases rightFresh : b = world.nextLoan
      · subst b
        have equal := Option.some.inj (selected.symm.trans second)
        subst right
        have conflict : Conflict access left.mode := by
          rcases unique with unique | unique
          · exact Or.inr unique
          · exact Or.inl (by intro shared; simp [fresh,shared] at unique)
        obtain ⟨parent,link,related⟩ := permission.conflicting_parent oldLeft leftLive (Address.Overlaps.symm overlap) conflict
        exact Or.inl (.parent selected link (ancestry related))
      · exact (overlaps a b left right oldLeft (old b right rightFresh second)
          leftLive rightLive overlap unique).elim (fun related => Or.inl (ancestry related))
          (fun related => Or.inr (ancestry related))
  · intro identity loan parent found link
    by_cases same : identity = world.nextLoan
    · subst identity
      have equal := Option.some.inj (selected.symm.trans found)
      subst loan
      obtain ⟨ancestor,atParent,active,included,mode⟩ := permission.parentLoan link
      exact ⟨ancestor,retained parent ancestor atParent,(bounds parent ancestor atParent).2.1,
        included,fun unique => mode (by intro shared; simp [fresh,shared] at unique),fun _ => active⟩
    · obtain ⟨ancestor,atParent,bound,included,mode,active⟩ := parents identity loan parent (old identity loan same found) link
      exact ⟨ancestor,retained parent ancestor atParent,bound,included,mode,active⟩
  · intro identity loan found live
    by_cases same : identity = world.nextLoan
    · subst identity
      have equal := Option.some.inj (selected.symm.trans found)
      subst loan
      exact located
    · exact locations identity loan (old identity loan same found) live
  · intro identity loan guard found member
    by_cases same : identity = world.nextLoan
    · subst identity
      have equal := Option.some.inj (selected.symm.trans found)
      subst loan
      obtain ⟨carrier,atGuard,live⟩ := permission.guardLoans guard member
      exact ⟨carrier,retained guard carrier atGuard,(bounds guard carrier atGuard).2.1,fun _ => live⟩
    · obtain ⟨carrier,atGuard,bound,live⟩ := guards identity loan guard (old identity loan same found) member
      exact ⟨carrier,retained guard carrier atGuard,bound,live⟩
  · intro identity loan found
    by_cases same : identity = world.nextLoan
    · subst identity
      have equal := Option.some.inj (selected.symm.trans found)
      subst loan
      exact kindAllowed
    · exact kinds identity loan (old identity loan same found)

theorem World.fresh_loan_worldTyped {program : Kernel.Program} {world : World}
    {authority : Authority} {access : Access} {address : Address} {region : Identity}
    (typed : Typing.WorldTyped program world)
    (permission : Permitted world authority access address) (located : world.Located address)
    (regionLive : region ∈ world.liveRegions) (kind : LoanKind) (custody : Option ClaimCustody)
    (kindAllowed : kind.Allows (if access = .shared then .shared else .unique) custody) :
    Typing.WorldTyped program
      { world with
        loans := world.loans.set world.nextLoan
          ⟨world.nextLoan,authority.parentLoan,address,
            if access = .shared then .shared else .unique,region,true,kind,
            authority.guardLoans world,false,custody⟩
        nextLoan := world.nextLoan+1 } := by
  let future : World := { world with
    loans := world.loans.set world.nextLoan
      ⟨world.nextLoan,authority.parentLoan,address,
        if access = .shared then .shared else .unique,region,true,kind,
        authority.guardLoans world,false,custody⟩
    nextLoan := world.nextLoan+1 }
  change Typing.WorldTyped program future
  refine ⟨world.fresh_loan_wellFormedWithOrigins typed.1 permission located regionLive kind custody kindAllowed,?_,typed.2.2⟩
  intro place value resident
  apply (typed.2.1 place value resident).transport (after := future) ?_ rfl
    (fun _ origin => origin.transport (fun _ => rfl))
  intro identity loan selected _
  exact ⟨(Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds typed.1 selected))).trans selected,
    fun _ located => located.retained (fun _ found => found) (fun _ => rfl)⟩

theorem World.root_region_live {world : World} {originBound : Identity} {address : Address} {root : Root}
    (valid : world.WellFormedWithOrigins originBound) (selected : world.root address = some root) :
    root.region ∈ world.liveRegions := by
  obtain ⟨found,live,_⟩ := World.root_found selected
  exact (valid.2.2.2.2.2.2.2.2.1 address.root root found).2.1 live

theorem ClaimsStorage.old_loan {custody : ClaimCustody} {before after : World}
    {authority : Authority} {access : Access} {address : Address} {created identity : Identity} {loan : Loan}
    (valid : before.WellFormed) (claimed : ClaimsStorage custody before authority access address created after)
    (found : before.loans.get identity = some loan) : after.loans.get identity = some loan := by
  cases claimed
  exact (Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid found))).trans found

theorem ClaimsStorage.worldTyped {program : Kernel.Program} {custody : ClaimCustody} {before after : World}
    {authority : Authority} {access : Access} {address : Address} {created : Identity}
    (typed : Typing.WorldTyped program before) (claimed : ClaimsStorage custody before authority access address created after) :
    Typing.WorldTyped program after := by
  cases claimed with
  | claim selected located permission =>
      exact before.fresh_loan_worldTyped typed permission located (before.root_region_live typed.1 selected) _ _
        (by simp [LoanKind.Allows])

theorem ClaimsAllocation.old_loan {custody : ClaimCustody} {before after : World}
    {authority : Authority} {address : Address} {created identity : Identity} {loan : Loan}
    (valid : before.WellFormed) (claimed : ClaimsAllocation custody before authority address created after)
    (found : before.loans.get identity = some loan) : after.loans.get identity = some loan := by
  cases claimed
  exact (Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid found))).trans found

theorem ClaimsAllocation.worldTyped {program : Kernel.Program} {custody : ClaimCustody} {before after : World}
    {authority : Authority} {address : Address} {created : Identity}
    (typed : Typing.WorldTyped program before) (claimed : ClaimsAllocation custody before authority address created after) :
    Typing.WorldTyped program after := by
  cases claimed with
  | claim owning permission selected =>
      obtain ⟨_,_,_,_,_,_,_,_,_,whole,_⟩ := owning
      exact before.fresh_loan_worldTyped typed permission ((World.Located.root_iff whole).mpr ⟨_,selected⟩)
        (before.root_region_live typed.1 selected) _ _ (by simp [LoanKind.Allows])

theorem ClaimsStorage.wellFormed {custody : ClaimCustody} {before after : World}
    {authority : Authority} {access : Access} {address : Address} {created : Identity}
    (valid : before.WellFormed) (claimed : ClaimsStorage custody before authority access address created after) :
    after.WellFormed := by
  cases claimed with
  | claim selected located permission =>
      exact before.fresh_loan_wellFormedWithOrigins valid permission located (before.root_region_live valid selected) _ _
        (by simp [LoanKind.Allows])

theorem ClaimsAllocation.wellFormed {custody : ClaimCustody} {before after : World}
    {authority : Authority} {address : Address} {created : Identity}
    (valid : before.WellFormed) (claimed : ClaimsAllocation custody before authority address created after) :
    after.WellFormed := by
  cases claimed with
  | claim owning permission selected =>
      obtain ⟨_,_,_,_,_,_,_,_,_,whole,_⟩ := owning
      exact before.fresh_loan_wellFormedWithOrigins valid permission ((World.Located.root_iff whole).mpr ⟨_,selected⟩)
        (before.root_region_live valid selected) _ _ (by simp [LoanKind.Allows])

theorem TransfersAllocation.wellFormed {recipient : ClaimCustody} {before after : World} {place : ResolvedPlace}
    (valid : before.WellFormed) (transferred : TransfersAllocation recipient before place after) :
    after.WellFormed := by
  cases transferred with
  | transfer _ _ found => exact before.set_loan_wellFormedWithOrigins valid found rfl (fun _ => rfl)

theorem TransfersStorageLoan.wellFormed {recipient : ClaimCustody} {before after : World} {place : ResolvedPlace}
    (valid : before.WellFormed) (transferred : TransfersStorageLoan recipient before place after) :
    after.WellFormed := by
  cases transferred with
  | unique _ found _ _ _ _ => exact before.set_loan_wellFormedWithOrigins valid found rfl (fun _ => rfl)
  | shared => exact valid

/-- Deactivation preserves the actual loan graph precisely when retained
live nodes retain their parent and guard dependencies, and resident handles
are not revoked. This is the shared lifecycle theorem for concrete release
rules; it never assumes the resulting world is well formed. -/
theorem World.loan_liveness_wellFormedWithOrigins {world : World} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) (keep : Loan → Bool)
    (referenced : ∀ identity loan, world.loans.get identity = some loan → loan.live = true →
      world.References identity → keep loan = true)
    (parentKept : ∀ identity loan parent ancestor, world.loans.get identity = some loan → loan.live = true →
      loan.parent = some parent → world.loans.get parent = some ancestor → keep loan = true → keep ancestor = true)
    (guardKept : ∀ identity loan guard carrier, world.loans.get identity = some loan → loan.live = true →
      guard ∈ loan.guards → world.loans.get guard = some carrier → keep loan = true → keep carrier = true) :
    World.WellFormedWithOrigins
      { world with loans := world.loans.map fun (identity,loan) => (identity,{ loan with live := keep loan && loan.live }) }
      originBound := by
  let update := fun loan : Loan => { loan with live := keep loan && loan.live }
  let future : World := { world with loans := world.loans.map fun (identity,loan) => (identity,update loan) }
  change future.WellFormedWithOrigins originBound
  have retained : ∀ identity loan, world.loans.get identity = some loan → future.loans.get identity = some (update loan) := by
    intro identity loan found
    exact (Table.get_map_values world.loans update identity).trans (by rw [found]; rfl)
  have reflected : ∀ identity current, future.loans.get identity = some current →
      ∃ original, world.loans.get identity = some original ∧ update original = current := by
    intro identity current found
    exact Option.map_eq_some_iff.mp ((Table.get_map_values world.loans update identity).symm.trans found)
  have ancestry : ∀ {a b}, AncestorLoan world a b → AncestorLoan future a b :=
    fun related => related.transport_parents (fun identity loan found => ⟨update loan,retained identity loan found,rfl⟩)
  obtain ⟨rootUnique,loanUnique,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
    roots,regions,bases,ranges,bounds,references,overlaps,parents,locations,guards,kinds⟩ := valid
  refine ⟨rootUnique,?_,proofUnique,regionUnique,?_,packs,owners,ownerUnique,
    roots,regions,bases,ranges,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [future,Table.Unique,List.map_map,Function.comp_def] using loanUnique
  · intro identity available found
    obtain ⟨same,bound,brand,active,recorded⟩ := proofs identity available found
    exact ⟨same,bound,brand,active,fun place member => (recorded place member).transport
      (fun identity loan found => ⟨update loan,retained identity loan found⟩)⟩
  · intro identity current found
    obtain ⟨original,selected,rfl⟩ := reflected identity current found
    obtain ⟨same,bound,active⟩ := bounds identity original selected
    exact ⟨same,bound,fun live => active (Bool.and_eq_true_iff.mp live).2⟩
  · intro address value identity resident head
    obtain ⟨loan,found,live⟩ := references address value identity resident head
    exact ⟨update loan,retained identity loan found,by
      change (keep loan && loan.live) = true
      simp only [referenced identity loan found live ⟨address,value,resident,head⟩,live,Bool.and_true]⟩
  · intro a b left right first second leftLive rightLive overlap unique
    obtain ⟨oldLeft,leftFound,rfl⟩ := reflected a left first
    obtain ⟨oldRight,rightFound,rfl⟩ := reflected b right second
    exact (overlaps a b oldLeft oldRight leftFound rightFound
      (Bool.and_eq_true_iff.mp leftLive).2 (Bool.and_eq_true_iff.mp rightLive).2 overlap unique).elim
      (fun related => Or.inl (ancestry related)) (fun related => Or.inr (ancestry related))
  · intro identity current parent found link
    obtain ⟨original,selected,rfl⟩ := reflected identity current found
    obtain ⟨ancestor,atParent,bound,included,mode,live⟩ := parents identity original parent selected link
    refine ⟨update ancestor,retained parent ancestor atParent,bound,included,mode,?_⟩
    intro active
    obtain ⟨kept,originalLive⟩ := Bool.and_eq_true_iff.mp active
    exact Bool.and_eq_true_iff.mpr ⟨parentKept identity original parent ancestor selected originalLive link atParent kept,
      live originalLive⟩
  · intro identity current found live
    obtain ⟨original,selected,rfl⟩ := reflected identity current found
    exact locations identity original selected (Bool.and_eq_true_iff.mp live).2
  · intro identity current guard found member
    obtain ⟨original,selected,rfl⟩ := reflected identity current found
    obtain ⟨carrier,atGuard,bound,live⟩ := guards identity original guard selected member
    refine ⟨update carrier,retained guard carrier atGuard,bound,?_⟩
    intro active
    obtain ⟨kept,originalLive⟩ := Bool.and_eq_true_iff.mp active
    exact Bool.and_eq_true_iff.mpr ⟨guardKept identity original guard carrier selected originalLive member atGuard kept,
      live originalLive⟩
  · intro identity current found
    obtain ⟨original,selected,rfl⟩ := reflected identity current found
    exact kinds identity original selected

theorem World.loan_liveness_worldTyped {program : Kernel.Program} {world : World}
    (typed : Typing.WorldTyped program world) (keep : Loan → Bool)
    (referenced : ∀ identity loan, world.loans.get identity = some loan → loan.live = true →
      world.References identity → keep loan = true)
    (parentKept : ∀ identity loan parent ancestor, world.loans.get identity = some loan → loan.live = true →
      loan.parent = some parent → world.loans.get parent = some ancestor → keep loan = true → keep ancestor = true)
    (guardKept : ∀ identity loan guard carrier, world.loans.get identity = some loan → loan.live = true →
      guard ∈ loan.guards → world.loans.get guard = some carrier → keep loan = true → keep carrier = true) :
    Typing.WorldTyped program
      { world with loans := world.loans.map fun (identity,loan) => (identity,{ loan with live := keep loan && loan.live }) } := by
  let future : World := { world with loans := world.loans.map fun (identity,loan) => (identity,{ loan with live := keep loan && loan.live }) }
  change Typing.WorldTyped program future
  refine ⟨world.loan_liveness_wellFormedWithOrigins typed.1 keep referenced parentKept guardKept,?_,typed.2.2⟩
  intro address value resident
  apply (typed.2.1 address value resident).transport_observed (after := future)
    (fun value => ∃ address, world.Resident address value)
    (fun _ _ ⟨_,present⟩ member => present.field member) ⟨address,resident⟩ ?_ ?_ (fun _ origin => origin)
  · intro current identity loan ⟨address,present⟩ head found active
    refine ⟨{ loan with live := keep loan && loan.live },?_,?_,rfl,rfl,?_⟩
    · exact (Table.get_map_values _ (fun loan : Loan => { loan with live := keep loan && loan.live }) _).trans (by rw [found])
    · exact Bool.and_eq_true_iff.mpr ⟨referenced identity loan found active ⟨address,current,present,head⟩,active⟩
    · intro type located
      exact located.retained (fun _ found => found) (fun _ => rfl)
  · exact fun _ original found => ⟨original,found,rfl,rfl,rfl⟩

theorem World.loan_root_parent_kept {world : World} {originBound root : Identity}
    (valid : world.WellFormedWithOrigins originBound) :
    ∀ identity loan parent ancestor, world.loans.get identity = some loan → loan.live = true →
      loan.parent = some parent → world.loans.get parent = some ancestor →
      decide (loan.referent.root ≠ root) = true → decide (ancestor.referent.root ≠ root) = true := by
  intro identity loan parent ancestor found _ link atParent kept
  obtain ⟨actual,selected,_,included,_⟩ := World.loanParents valid identity loan parent found link
  have same := Option.some.inj (selected.symm.trans atParent)
  subst actual
  simpa only [included.1] using kept

theorem ReleasesStorageClaims.as_liveness {before after : World} {place : ResolvedPlace}
    (released : ReleasesStorageClaims before place after) :
    after = { before with loans := before.loans.map fun (identity,loan) =>
      (identity,{ loan with live := decide (loan.referent.root ≠ place.address.root) && loan.live }) } := by
  cases released
  congr 1
  apply List.map_congr_left
  intro ⟨identity,loan⟩ _
  by_cases same : loan.referent.root = place.address.root
  · simp [same]
  · simp [same]

theorem ReleasesStorageClaims.keep_references {before after : World} {place : ResolvedPlace}
    (released : ReleasesStorageClaims before place after) :
    ∀ identity loan, before.loans.get identity = some loan → loan.live = true →
      before.References identity → decide (loan.referent.root ≠ place.address.root) = true := by
  cases released with
  | release ready =>
      intro identity loan selected live referenced
      simp only [decide_eq_true_eq]
      intro removed
      exact (ready.safe identity loan selected live removed).2.1 referenced

theorem ReleasesStorageClaims.keep_guards {before after : World} {place : ResolvedPlace}
    (released : ReleasesStorageClaims before place after) :
    ∀ identity loan guard carrier, before.loans.get identity = some loan → loan.live = true →
      guard ∈ loan.guards → before.loans.get guard = some carrier →
      decide (loan.referent.root ≠ place.address.root) = true → decide (carrier.referent.root ≠ place.address.root) = true := by
  cases released with
  | release ready =>
      intro identity loan guard carrier selected live member found kept
      simp only [decide_eq_true_eq] at kept ⊢
      exact fun removed => kept (ready.dependencies identity loan guard carrier selected live member found removed)

theorem ReleasesStorageClaims.wellFormed {before after : World} {place : ResolvedPlace}
    (valid : before.WellFormed) (released : ReleasesStorageClaims before place after) : after.WellFormed := by
  rw [released.as_liveness]
  exact before.loan_liveness_wellFormedWithOrigins valid _ released.keep_references
    (before.loan_root_parent_kept valid) released.keep_guards

theorem ReleasesStorageClaims.worldTyped {program : Kernel.Program} {before after : World} {place : ResolvedPlace}
    (typed : Typing.WorldTyped program before) (released : ReleasesStorageClaims before place after) :
    Typing.WorldTyped program after := by
  rw [released.as_liveness]
  exact before.loan_liveness_worldTyped typed _ released.keep_references
    (before.loan_root_parent_kept typed.1) released.keep_guards

theorem World.set_loan_dead_lookup {world : World} {identity : Identity} {loan : Loan}
    (valid : world.WellFormed) (selected : world.loans.get identity = some loan) (key : Identity) :
    (world.loans.set identity { loan with live := false }).get key =
      Table.get (world.loans.map fun (key,original) =>
        (key,{ original with live := decide (original.identity ≠ identity) && original.live })) key := by
  refine Eq.trans ?_ (Table.get_map_values world.loans (fun original : Loan =>
    { original with live := decide (original.identity ≠ identity) && original.live }) key).symm
  by_cases same : key = identity
  · subst key
    rw [Table.get_set,selected]
    have actual : loan.identity = identity := (World.loanIdentity valid selected).symm
    simp only [actual,ne_eq,not_true_eq_false,decide_false,Bool.false_and,Option.map_some]
  · rw [Table.get_set_other _ _ _ _ same]
    cases found : world.loans.get key with
    | none => rfl
    | some original =>
        have actual : original.identity = key := (World.loanIdentity valid found).symm
        simp only [actual,same,ne_eq,not_false_eq_true,decide_true,Bool.true_and,Option.map_some]
        rw [← actual]

/-- Source-reference ending and erased storage-loan return share exactly the
same dead-row operation. Their distinct restoration/return-request admission
rules supply these common quiescence facts. -/
theorem World.set_loan_dead_wellFormed {world : World} {identity : Identity} {loan : Loan}
    (valid : world.WellFormed) (selected : world.loans.get identity = some loan)
    (unreferenced : ¬ world.References identity)
    (children : ∀ child, world.loans.get child.identity = some child →
      child.parent = some identity ∨ identity ∈ child.guards → child.live = false) :
    World.WellFormed { world with loans := world.loans.set identity { loan with live := false } } := by
  have mapped := world.loan_liveness_wellFormedWithOrigins valid (fun original => decide (original.identity ≠ identity))
    (by
      intro key original found _ referenced
      simp only [decide_eq_true_eq]
      exact fun same => unreferenced ((World.loanIdentity valid found).trans same ▸ referenced))
    (by
      intro key child parent ancestor found live link atParent _
      simp only [decide_eq_true_eq]
      intro same
      have parentEq := (World.loanIdentity valid atParent).trans same
      have dead := children child (by simpa only [World.loanIdentity valid found] using found)
        (Or.inl (link.trans (congrArg some parentEq)))
      rw [dead] at live
      cases live)
    (by
      intro key child guard carrier found live member atGuard _
      simp only [decide_eq_true_eq]
      intro same
      have guardEq := (World.loanIdentity valid atGuard).trans same
      have dead := children child (by simpa only [World.loanIdentity valid found] using found) (Or.inr (guardEq ▸ member))
      rw [dead] at live
      cases live)
  apply World.loan_table_wellFormedWithOrigins mapped (valid.2.1.set _ _)
  · intro key current found
    exact ⟨current,(world.set_loan_dead_lookup valid selected key).trans found,rfl⟩
  · intro key current found
    exact ⟨current,(world.set_loan_dead_lookup valid selected key).symm.trans found,rfl⟩
  · intro key original current found changed present
    have old := (world.set_loan_dead_lookup valid selected key).symm.trans changed
    have same := Option.some.inj (found.symm.trans old)
    exact same ▸ present

theorem World.set_loan_dead_worldTyped {program : Kernel.Program} {world : World} {identity : Identity} {loan : Loan}
    (typed : Typing.WorldTyped program world) (selected : world.loans.get identity = some loan)
    (unreferenced : ¬ world.References identity)
    (children : ∀ child, world.loans.get child.identity = some child →
      child.parent = some identity ∨ identity ∈ child.guards → child.live = false) :
    Typing.WorldTyped program { world with loans := world.loans.set identity { loan with live := false } } := by
  refine ⟨world.set_loan_dead_wellFormed typed.1 selected unreferenced children,?_,typed.2.2⟩
  intro address value resident
  apply (typed.2.1 address value resident).resident_transport
    (after := { world with loans := world.loans.set identity { loan with live := false } })
    ?_ rfl (fun _ origin => origin) ⟨address,resident⟩
  intro key original referenced found _
  have different : key ≠ identity := fun same => unreferenced (same ▸ referenced)
  exact ⟨(Table.get_set_other _ _ _ _ different).trans found,
    fun _ located => located.retained (fun _ found => found) (fun _ => rfl)⟩

theorem ReturnsStorageLoan.wellFormed {before after : World} {identity : Identity}
    (valid : before.WellFormed) (returned : ReturnsStorageLoan before identity after) : after.WellFormed := by
  cases returned with
  | returned found _ _ _ unreferenced _ children => exact before.set_loan_dead_wellFormed valid found unreferenced children

theorem ReturnsStorageLoan.worldTyped {program : Kernel.Program} {before after : World} {identity : Identity}
    (typed : Typing.WorldTyped program before) (returned : ReturnsStorageLoan before identity after) :
    Typing.WorldTyped program after := by
  cases returned with
  | returned found _ _ _ unreferenced _ children => exact before.set_loan_dead_worldTyped typed found unreferenced children

theorem EndsLoan.wellFormed {program : RuntimeProgram} {before after : World} {identity : Identity}
    (valid : before.WellFormed) (ended : EndsLoan program before identity after) : after.WellFormed := by
  cases ended with
  | restored found _ _ _ _ unreferenced _ children => exact before.set_loan_dead_wellFormed valid found unreferenced children

theorem EndsLoan.worldTyped {program : Kernel.Program} {before after : World} {identity : Identity}
    (typed : Typing.WorldTyped program before) (ended : EndsLoan program.toRuntimeProgram before identity after) :
    Typing.WorldTyped program after := by
  cases ended with
  | restored found _ _ _ _ unreferenced _ children => exact before.set_loan_dead_worldTyped typed found unreferenced children


/-- Ending a different row removes an exclusion; it cannot supersede the
latest live owning claim. Parent links survive the actual dead-row update. -/
theorem AllocationClaim.end_loan {before : World} {id : Identity} {ended : Loan}
    {authority : Authority} {address : Address}
    (found : before.loans.get id = some ended) (outside : authority.parentLoan ≠ some id)
    (claim : AllocationClaim before authority address) :
    AllocationClaim { before with loans := before.loans.set id { ended with live := false } } authority address := by
  obtain ⟨identity,loan,root,domain,parent,selected,live,kind,referent,whole,rootAt,home,latest⟩ := claim
  have different : identity ≠ id := fun same => outside (parent.trans (congrArg some same))
  refine ⟨identity,loan,root,domain,parent,?_,live,kind,referent,whole,rootAt,home,?_⟩
  · rw [Table.get_set_other _ _ _ _ different]
    exact selected
  · intro child successor childAt childLive childKind related
    have prior : AncestorLoan before identity child := by
      apply related.transport_parents
      intro key current currentAt
      by_cases same : key = id
      · subst key
        have equal : current = { ended with live := false } :=
          Option.some.inj (currentAt.symm.trans (Table.get_set _ _ _))
        exact ⟨ended,found,by rw [equal]⟩
      · exact ⟨current,by simpa only [Table.get_set_other _ _ _ _ same] using currentAt,rfl⟩
    by_cases same : child = id
    · subst child
      have equal : successor = { ended with live := false } :=
        Option.some.inj (childAt.symm.trans (Table.get_set _ _ _))
      rw [equal] at childLive
      cases childLive
    · exact latest child successor (by simpa only [Table.get_set_other _ _ _ _ same] using childAt)
        childLive childKind prior

theorem StorageBinding.HeldBy.end_loan {before : World} {id : Identity} {ended : Loan}
    {binding : StorageBinding} {owner : Identity}
    (found : before.loans.get id = some ended) (outside : binding.authority.parentLoan ≠ some id)
    (held : binding.HeldBy before owner) :
    binding.HeldBy { before with loans := before.loans.set id { ended with live := false } } owner := by
  refine ⟨Authority.Custodied.of_row_change rfl (fun same => False.elim (outside same)) held.1,?_⟩
  rcases held.2 with ⟨claim,readOnly⟩ | ⟨identity,loan,parent,selected,live,kind,referent,shared⟩
  · exact Or.inl ⟨claim.end_loan found outside,readOnly⟩
  · have different : identity ≠ id := fun same => outside (parent.trans (congrArg some same))
    exact Or.inr ⟨identity,loan,parent,by rw [Table.get_set_other _ _ _ _ different]; exact selected,
      live,kind,referent,shared⟩

/-- The real ending guards exclude its identity from every stored handoff
resource graph. The existing batch product, not a second reachability walk,
therefore retains the graph's reference rows and held resources. -/
theorem Value.BatchCompatible.end_loan {before : World} {address : Address} {value : Value}
    {id : Identity} {ended : Loan} (source : before.Stores address value)
    (found : before.loans.get id = some ended)
    (references : ¬ before.References id) (resources : ¬ before.ResourceReferences id) :
    value.BatchCompatible before { before with loans := before.loans.set id { ended with live := false } } := by
  constructor
  · intro identity current access reached
    have different : identity ≠ id := fun same => references (same ▸ reached.worldReference source)
    rw [Table.get_set_other _ _ _ _ different]
  · intro resident authority access reached binding member held
    obtain ⟨observed,located⟩ := reached.worldResident source
    have outside : binding.authority.parentLoan ≠ some id :=
      fun parent => resources ⟨observed,resident,binding,located,member,parent⟩
    exact held.end_loan found outside

/-- Source restoration remains true through an actual loan ending. Stored
referents and invariant support do not move; the ending's global reference
and resource guards provide the canonical batch frame for every stored value. -/
theorem World.ResourcesClosed.end_loan {program : RuntimeProgram} {before : World}
    {address : Address} {id : Identity} {ended : Loan}
    (found : before.loans.get id = some ended)
    (references : ¬ before.References id) (resources : ¬ before.ResourceReferences id)
    (closed : before.ResourcesClosed program address) :
    World.ResourcesClosed program { before with loans := before.loans.set id { ended with live := false } } address := by
  intro value stored
  have source : before.Stores address value := stored
  obtain ⟨valueClosed,restored⟩ := closed value source
  have batch := Value.BatchCompatible.end_loan source found references resources
  have framed : value.SupportFramed before { before with loans := before.loans.set id { ended with live := false } } :=
    fun _ _ => ⟨rfl,rfl⟩
  exact ⟨valueClosed.frame_batch batch framed,restored.frame_batch batch framed⟩



/-- A real row map retaining permission geometry and custody also retains
allocation claims. This is the common resource product for pending-return
administration, not an assumed unchanged loan table. -/
theorem World.map_loans_resourceRows {world : World} {map : Loan → Loan}
    (shape : ∀ loan, (map loan).permissionState = loan.permissionState)
    (custody : ∀ loan, (map loan).custody = loan.custody) :
    world.ResourceRowsRetained { world with loans := world.loans.map fun (key,loan) => (key,map loan) } := by
  let after : World := { world with loans := world.loans.map fun (key,loan) => (key,map loan) }
  have atRow : ∀ id loan, world.loans.get id = some loan → after.loans.get id = some (map loan) := by
    intro id loan found
    exact (Table.get_map_values world.loans map id).trans (by rw [found]; rfl)
  have origin : ∀ id current, after.loans.get id = some current →
      ∃ loan, world.loans.get id = some loan ∧ current = map loan := by
    intro id current found
    obtain ⟨loan,selected,same⟩ := Option.map_eq_some_iff.mp
      ((Table.get_map_values world.loans map id).symm.trans found)
    exact ⟨loan,selected,same.symm⟩
  refine ⟨world.map_loans_retained shape,?_,?_⟩
  · intro authority address claim
    obtain ⟨id,loan,root,domain,parent,found,live,kind,referent,whole,rootAt,home,latest⟩ := claim
    obtain ⟨_,_,sameReferent,_,_,sameLive,sameKind,_⟩ := Loan.permissionState_eq_iff.mp (shape loan)
    refine ⟨id,map loan,root,domain,parent,atRow id loan found,sameLive.trans live,sameKind.trans kind,
      sameReferent.trans referent,whole,rootAt,home,?_⟩
    intro child current currentAt currentLive currentKind related
    obtain ⟨original,originalAt,rfl⟩ := origin child current currentAt
    obtain ⟨_,_,_,_,_,liveEq,kindEq,_⟩ := Loan.permissionState_eq_iff.mp (shape original)
    apply latest child original originalAt (liveEq.symm.trans currentLive) (kindEq.symm.trans currentKind)
    apply related.transport_parents
    intro key current found
    obtain ⟨original,selected,rfl⟩ := origin key current found
    exact ⟨original,selected,(Loan.permissionState_eq_iff.mp (shape original)).2.1.symm⟩
  · intro authority owner held
    induction authority with
    | owner => trivial
    | loan id =>
        obtain ⟨loan,found,allowed⟩ := held
        have kind := (Loan.permissionState_eq_iff.mp (shape loan)).2.2.2.2.2.2.1
        exact ⟨map loan,atRow id loan found,by simpa only [kind,custody] using allowed⟩
    | shared backing => exact held.transport (fun id loan found => ⟨map loan,atRow id loan found⟩)
    | guarded backing carrier ih => exact ih held

theorem RelinquishesCustody.resourceRows {before after : World} {custody : ClaimCustody}
    (relinquished : RelinquishesCustody before custody after) : before.ResourceRowsRetained after := by
  cases relinquished
  exact World.map_loans_resourceRows
    (map := fun loan => if loan.custody = some custody ∧ loan.kind = .storageBorrow then
      { loan with returnRequested := true } else loan)
    (fun _ => by split <;> rfl) (fun _ => by split <;> rfl)

theorem World.ResourcesClosed.relinquished {program : RuntimeProgram} {before after : World}
    {custody : ClaimCustody} {address : Address}
    (relinquished : RelinquishesCustody before custody after) (closed : before.ResourcesClosed program address) :
    after.ResourcesClosed program address := by
  have reads : ∀ address, after.read address = before.read address := by cases relinquished; intro; rfl
  intro value stored
  have original : before.Stores address value := (reads address).symm.trans stored
  obtain ⟨resources,restored⟩ := closed value original
  have batch : value.BatchCompatible before after := by
    apply Value.BatchCompatible.of_rows relinquished.resourceRows
    intro identity current access reached
    obtain ⟨loan,found,_⟩ := restored identity current access reached
    exact ⟨loan,found⟩
  have framed : value.SupportFramed before after := by cases relinquished; exact fun _ _ => ⟨rfl,rfl⟩
  exact ⟨resources.frame_batch batch framed,restored.frame_batch batch framed⟩


end Glorious.Language
