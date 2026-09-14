import GloriousLanguage.HandoffAccess
import GloriousLanguage.ClearPreservation

/-! A move preserves its actual reference/resource graph and declared closed
invariants. Support and permissions come from the real pre-state handoff;
read equality is derived from clear/install, never from a typed post-state. -/
namespace Glorious.Language

/-- Storage may gain fresh roots while retaining every previously recorded
location. This is the common forward frame used by allocation and handoff;
it does not assert that fresh storage was present in the source world. -/
def World.LocationExtension (before after : World) : Prop :=
  ∀ identity root, before.roots.get identity = some root →
    (after.roots.get identity).map Root.location = some root.location

theorem World.LocationExtension.of_locations {before after : World}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location) :
    before.LocationExtension after := by
  intro identity root selected
  rw [locations,selected]
  rfl

theorem World.LocationExtension.refl (world : World) : world.LocationExtension world := by
  intro identity root selected
  rw [selected]
  rfl

theorem World.LocationExtension.trans {before middle after : World}
    (first : before.LocationExtension middle) (last : middle.LocationExtension after) :
    before.LocationExtension after := by
  intro identity root selected
  obtain ⟨resident,found,same⟩ := Option.map_eq_some_iff.mp (first identity root selected)
  exact (last identity resident found).trans (congrArg some same)

theorem World.LocationExtension.root {before after : World} {address : Address} {root : Root}
    (locations : before.LocationExtension after) (selected : before.root address = some root) :
    ∃ resident, after.root address = some resident ∧ resident.location = root.location := by
  obtain ⟨found,live,generation⟩ := World.root_found selected
  obtain ⟨resident,changed,same⟩ := Option.map_eq_some_iff.mp (locations address.root root found)
  have residentGeneration : resident.generation = root.generation := by simpa [Root.location] using congrArg Root.generation same
  have residentLive : resident.live = root.live := by simpa [Root.location] using congrArg Root.live same
  exact ⟨resident,by simp [World.root,changed,residentLive,live,residentGeneration,generation],same⟩

theorem Permitted.locationExtension {before after : World} {authority : Authority} {access : Access} {address : Address}
    (locations : before.LocationExtension after) (loans : after.loans = before.loans)
    (permission : Permitted before authority access address) : Permitted after authority access address := by
  obtain ⟨root,selected⟩ := permission.root
  obtain ⟨changed,found,_⟩ := locations.root selected
  induction authority with
  | owner => exact ⟨⟨changed,found⟩,by simpa only [loans] using permission.2⟩
  | loan id => exact ⟨⟨changed,found⟩,permission.2.transport loans⟩
  | shared backing ih => exact ⟨⟨changed,found⟩,permission.2.1,ih permission.2.2⟩
  | guarded backing carrier ih =>
      obtain ⟨loan,selected,guard⟩ := permission.2.2
      exact ⟨⟨changed,found⟩,ih permission.2.1,loan,by simpa only [loans] using selected,guard.transport loans⟩

/-- The common rebasing producer identifies the sole extra authority of a
borrowed view and preserves its access bound at every reached resident. -/
theorem Value.ReachableResident.loan_view {world : World} {value resident : Value}
    {identity : Identity} {current : Authority} {incoming access : Access}
    (reached : value.ReachableResident world ((Authority.loan identity).lend incoming) incoming resident current access) :
    ∃ base, value.ReachableResident world .owner incoming resident base access ∧
      current.carriers = identity :: base.carriers ∧ (access ≠ .shared → incoming ≠ .shared) := by
  obtain ⟨base,nextAccess,prior,⟨trail,original,rebased⟩,same,shared⟩ := reached.rebase_carriers .owner incoming
  have equal := same rfl
  subst nextAccess
  simp only [Authority.carriers_lend,Authority.carriers,List.nil_append,List.singleton_append] at original rebased
  rw [← rebased] at original
  exact ⟨base,prior,original,fun nonshared initialShared => nonshared (shared initialShared)⟩

/-- A permitted borrower adds its explicit carrier to the existing reachable
permissions. The original graph and access bounds come from the common
rebasing producer, not a separately reconstructed resource inventory. -/
theorem Value.ResourcesAccessible.loan_permissions {program : RuntimeProgram} {world : World} {value : Value}
    {identity : Identity} {loan : Loan} {incoming : Access}
    (ready : value.ResourcesAccessible program world incoming)
    (found : world.loans.get identity = some loan) (carrier : LoanPermission world identity incoming loan.referent) :
    value.ReferencesAccessible world ((Authority.loan identity).lend incoming) incoming ∧
      ∀ resident current access, value.ReachableResident world ((Authority.loan identity).lend incoming) incoming resident current access →
        ∀ binding ∈ resident.resources, Permitted world (current.resourceView binding access) (ResourceAccess access binding) binding.address := by
  constructor
  · intro nested current access reached
    obtain ⟨resident,reached,head⟩ := reached
    obtain ⟨base,prior,carriers,weaker⟩ := reached.loan_view
    obtain ⟨selected,selectedFound,live,permission⟩ := ready.references nested base access ⟨resident,prior,head⟩
    refine ⟨selected,selectedFound,live,Permitted.referenceView_iff.mpr ?_⟩
    obtain ⟨backing,existing⟩ := Permitted.referenceView_iff.mp permission
    refine ⟨backing,?_⟩
    intro guardian member
    rw [carriers] at member
    rcases List.mem_cons.mp member with rfl | member
    · refine ⟨loan,found,carrier.weaken ?_⟩
      intro nonshared
      apply weaker
      intro shared
      exact nonshared (by simp only [ReferenceAccess,shared,true_or,ite_true])
    · exact existing guardian member
  · intro resident current access reached binding member
    obtain ⟨base,prior,carriers,weaker⟩ := reached.loan_view
    obtain ⟨backing,existing⟩ := Permitted.resourceView_iff.mp (ready.2.2.2 resident base access prior binding member)
    apply Permitted.resourceView_iff.mpr
    refine ⟨backing,?_⟩
    intro guardian inside
    rw [carriers] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · refine ⟨loan,found,carrier.weaken ?_⟩
      intro nonshared
      apply weaker
      intro shared
      apply nonshared
      rw [shared]
      unfold ResourceAccess
      split <;> rfl
    · exact existing guardian inside


/-- A materialized reference has no resident fields or resources. Its graph
is exactly its root plus the actual stored referent's graph at the reference
view; neither a guessed row nor an invented edge can enter this decomposition. -/
theorem Value.ReachableResident.reference_cases {world : World} {owner identity : Identity}
    {type : Term} {loan : Loan} {target resident : Value} {current : Authority} {incoming access : Access}
    (found : world.loans.get identity = some loan) (stored : world.Stores loan.referent target)
    (reached : (Value.resident owner type (.reference identity) true []).ReachableResident world .owner incoming resident current access) :
    (resident = .resident owner type (.reference identity) true [] ∧ current = .owner ∧ access = incoming) ∨
      target.ReachableResident world ((Authority.loan identity).lend (ReferenceAccess incoming loan.mode))
        (ReferenceAccess incoming loan.mode) resident current access := by
  induction reached with
  | resident located =>
    cases located with
    | root => exact Or.inl ⟨rfl,rfl,rfl⟩
    | field field _ => simp [Value.fields] at field
  | @referent carrier parent parentAuthority parentAccess actual actualTarget path resident prior reference selected read located ih =>
    rcases ih with ⟨rfl,rfl,rfl⟩ | nested
    · have parentEq : parent = identity := by simpa [Value.head] using reference.symm
      subst parent
      have loanEq := Option.some.inj (selected.symm.trans found)
      subst actual
      have targetEq := Option.some.inj (read.symm.trans stored)
      subst actualTarget
      exact Or.inr (.resident located)
    · exact Or.inr (.referent nested reference selected read located)
  | resource prior member read located ih =>
    rcases ih with ⟨rfl,rfl,rfl⟩ | nested
    · simp [Value.resources] at member
    · exact Or.inr (.resource nested member read located)

/-- Closure, restored initialization and every nested permission compose into
readiness of the actual reference resident. The referent's graph is traversed
through its borrower, including all explicit carrier permissions. -/
theorem Value.ResourcesAccessible.reference {program : RuntimeProgram} {world : World}
    {owner identity : Identity} {type : Term} {loan : Loan} {target : Value} {incoming : Access}
    (found : world.loans.get identity = some loan) (stored : world.Stores loan.referent target)
    (initialized : target.Initialized)
    (ready : target.ResourcesAccessible program world (ReferenceAccess incoming loan.mode))
    (permission : Permitted world (.loan identity) (ReferenceAccess incoming loan.mode) loan.referent) :
    (Value.resident owner (.reference loan.mode (.runtimeRegion loan.region) type) (.reference identity) true []).ResourcesAccessible program world incoming := by
  have live : loan.live = true := by
    obtain ⟨actual,selected,live,_⟩ := permission.2
    have same := Option.some.inj (selected.symm.trans found)
    exact same ▸ live
  obtain ⟨references,resources⟩ := ready.loan_permissions found permission.2
  refine ⟨?_,?_,?_,?_⟩
  · intro resident current access reached
    rcases reached.reference_cases found stored with ⟨rfl,rfl,rfl⟩ | nested
    · exact ⟨by simp [Value.resources],rfl⟩
    · obtain ⟨base,requested,nested⟩ := nested.rebase .owner .shared
      exact ready.1 resident base requested nested
  · rintro nested current access ⟨node,reached,head⟩
    rcases reached.reference_cases found stored with ⟨rfl,rfl,rfl⟩ | nestedReach
    · have same : nested = identity := by simpa [Value.head] using head.symm
      subst nested
      refine ⟨loan,found,live,⟨target,stored,initialized⟩,?_⟩
      intro actual selected
      have same := Option.some.inj (selected.symm.trans stored)
      exact same ▸ ready.1
    · obtain ⟨base,requested,nestedReach⟩ := nestedReach.rebase .owner .shared
      exact ready.2.1 nested base requested ⟨node,nestedReach,head⟩
  · rintro nested current access ⟨node,reached,head⟩
    rcases reached.reference_cases found stored with ⟨rfl,rfl,rfl⟩ | nestedReach
    · have same : nested = identity := by simpa [Value.head] using head.symm
      subst nested
      exact ⟨loan,found,live,Permitted.lend_iff.mpr permission⟩
    · exact references nested current access ⟨node,nestedReach,head⟩
  · intro resident current access reached binding member
    rcases reached.reference_cases found stored with ⟨rfl,rfl,rfl⟩ | nested
    · simp [Value.resources] at member
    · exact resources resident current access nested binding member


theorem Value.ReachableResident.nested {world : World} {value carrier resident : Value}
    {authority current : Authority} {incoming access : Access} {path : List Nat}
    (reached : value.ReachableResident world authority incoming carrier current access)
    (located : ResidentAt carrier path resident) :
    value.ReachableResident world authority incoming resident current access := by
  induction reached with
  | resident initial => exact .resident (initial.append located)
  | referent prior reference found stored initial _ => exact .referent prior reference found stored (initial.append located)
  | resource prior member stored initial _ => exact .resource prior member stored (initial.append located)

theorem Value.ReachableResident.trans {world : World} {value carrier resident : Value}
    {authority current final : Authority} {incoming access finalAccess : Access}
    (prior : value.ReachableResident world authority incoming carrier current access)
    (next : carrier.ReachableResident world current access resident final finalAccess) :
    value.ReachableResident world authority incoming resident final finalAccess := by
  induction next with
  | resident located => exact prior.nested located
  | referent _ reference found stored located ih => exact .referent ih reference found stored located
  | resource _ member stored located ih => exact .resource ih member stored located

theorem Value.ResourcesClosed.reachable {program : RuntimeProgram} {world : World}
    {value resident : Value} {authority current : Authority} {incoming access : Access}
    (closed : value.ResourcesClosed program world)
    (reached : value.ReachableResident world authority incoming resident current access) :
    resident.ResourcesClosed program world := by
  intro child next requested nested
  obtain ⟨base,access,prior⟩ := reached.rebase .owner .shared
  obtain ⟨final,finalAccess,nested⟩ := nested.rebase base access
  exact closed child final finalAccess (prior.trans nested)

theorem Value.LoansRestored.reachable {program : RuntimeProgram} {world : World}
    {value resident : Value} {authority current : Authority} {incoming access : Access}
    (restored : value.LoansRestored program world)
    (reached : value.ReachableResident world authority incoming resident current access) :
    resident.LoansRestored program world := by
  rintro identity next requested ⟨child,nested,head⟩
  obtain ⟨base,access,prior⟩ := reached.rebase .owner .shared
  obtain ⟨final,finalAccess,nested⟩ := nested.rebase base access
  exact restored identity final finalAccess ⟨child,prior.trans nested,head⟩

theorem Value.InvariantClosed.framed {program : RuntimeProgram} {before after : World} {value : Value}
    (framed : value.SupportFramed before after) (closed : value.InvariantClosed program before) :
    value.InvariantClosed program after := by
  unfold Value.InvariantClosed at closed ⊢
  cases type : value.type with
  | nominal identity arguments =>
      simp only [type] at closed ⊢
      obtain ⟨data,found,declared⟩ := closed
      refine ⟨data,found,?_⟩
      cases invariant : data.invariant with
      | none => simpa only [invariant] using declared
      | some invariant =>
          simp only [invariant] at declared ⊢
          obtain ⟨contract,found,owner,holds⟩ := declared
          exact ⟨contract,found,owner,contract.framed before after value framed holds⟩
  | _ => simpa only [type] using closed

theorem Value.Support.reference {world : World} {value : Value} {authority current : Authority}
    {incoming access : Access} {identity : Identity} {loan : Loan}
    (reachable : value.ReachableReference world authority incoming identity current access)
    (found : world.loans.get identity = some loan) : value.Support world loan.referent := by
  obtain ⟨resident,reached,reference⟩ := reachable
  obtain ⟨next,nextAccess,reached⟩ := reached.rebase .owner .shared
  exact ⟨resident,next,nextAccess,reached,Or.inl ⟨identity,loan,reference,found,rfl⟩⟩

theorem Value.Support.resource {world : World} {value resident : Value} {authority current : Authority}
    {incoming access : Access} {binding : StorageBinding}
    (reachable : value.ReachableResident world authority incoming resident current access)
    (member : binding ∈ resident.resources) : value.Support world binding.address := by
  obtain ⟨next,nextAccess,reached⟩ := reachable.rebase .owner .shared
  exact ⟨resident,next,nextAccess,reached,Or.inr ⟨binding,member,rfl⟩⟩

theorem Value.Support.reachable {world : World} {value resident : Value} {authority current : Authority}
    {incoming access : Access} {address : Address}
    (reachable : value.ReachableResident world authority incoming resident current access)
    (supported : resident.Support world address) : value.Support world address := by
  obtain ⟨carrier,next,nextAccess,reached,edge⟩ := supported
  obtain ⟨base,requested,prior⟩ := reachable.rebase .owner .shared
  obtain ⟨final,finalAccess,reached⟩ := reached.rebase base requested
  exact ⟨carrier,final,finalAccess,prior.trans reached,edge⟩

theorem Value.SupportFramed.reachable {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (framed : value.SupportFramed before after)
    (reachable : value.ReachableResident before authority incoming resident current access) :
    resident.SupportFramed before after :=
  fun address supported => framed address (supported.reachable reachable)

theorem Authority.Recorded.lend {authority : Authority} {loans : Table Loan}
    (recorded : authority.Recorded loans) (access : Access) : (authority.lend access).Recorded loans := by
  unfold Authority.lend
  split <;> exact recorded

theorem Authority.Recorded.of_lend {authority : Authority} {loans : Table Loan} {access : Access}
    (recorded : (authority.lend access).Recorded loans) : authority.Recorded loans := by
  unfold Authority.lend at recorded
  split at recorded <;> exact recorded

theorem Authority.Recorded.guarded_fold {authority : Authority} {loans : Table Loan} {guards : List Identity}
    (recorded : authority.Recorded loans)
    (known : ∀ identity ∈ guards, ∃ loan, loans.get identity = some loan) :
    (guards.foldr (fun carrier backing => Authority.guarded backing carrier) authority).Recorded loans := by
  induction guards with
  | nil => exact recorded
  | cons carrier rest ih => exact ⟨ih (fun identity member => known identity (List.mem_cons_of_mem _ member)),
      known carrier List.mem_cons_self⟩

theorem Authority.Recorded.of_guarded_fold {authority : Authority} {loans : Table Loan} {guards : List Identity}
    (recorded : (guards.foldr (fun carrier backing => Authority.guarded backing carrier) authority).Recorded loans) :
    authority.Recorded loans := by
  induction guards with
  | nil => exact recorded
  | cons carrier rest ih => exact ih recorded.1

theorem Authority.Recorded.guardLoans {world : World} {authority : Authority}
    (valid : world.WellFormed) (recorded : authority.Recorded world.loans) :
    ∀ guard ∈ authority.guardLoans world, ∃ loan, world.loans.get guard = some loan := by
  induction authority with
  | owner => intro guard member; simp [Authority.guardLoans] at member
  | loan identity =>
      obtain ⟨loan,found⟩ := recorded
      intro guard member
      have inside : guard ∈ loan.guards := by simpa only [Authority.guardLoans,found,Option.map_some,Option.getD_some] using member
      obtain ⟨carrier,selected,_⟩ := World.loanGuards valid identity loan guard found inside
      exact ⟨carrier,selected⟩
  | shared backing ih => exact ih recorded
  | guarded backing carrier ih =>
      obtain ⟨loan,found⟩ := recorded.2
      intro guard member
      simp only [Authority.guardLoans,found,Option.map_some,Option.getD_some,List.mem_append,List.mem_cons] at member
      rcases member with (rfl | member) | member
      · exact ⟨loan,found⟩
      · obtain ⟨current,selected,_⟩ := World.loanGuards valid carrier loan guard found member
        exact ⟨current,selected⟩
      · exact ih recorded.1 guard member

theorem Authority.Recorded.referenceView {world : World} {authority : Authority} {identity : Identity} {loan : Loan}
    (recorded : authority.Recorded world.loans)
    (found : world.loans.get identity = some loan) (access : Access) :
    (authority.referenceView identity access).Recorded world.loans := by
  apply Authority.Recorded.lend
  exact Authority.Recorded.guarded_fold (authority := .loan identity) ⟨loan,found⟩ recorded.carriers

theorem Authority.Recorded.resourceView {world : World} {authority : Authority} {binding : StorageBinding}
    (recorded : authority.Recorded world.loans)
    (resource : binding.authority.Recorded world.loans) (access : Access) :
    (authority.resourceView binding access).Recorded world.loans := by
  apply Authority.Recorded.lend
  exact Authority.Recorded.guarded_fold resource recorded.carriers


theorem Authority.Recorded.resourceView_backing {world : World} {authority : Authority} {binding : StorageBinding} {access : Access}
    (recorded : (authority.resourceView binding access).Recorded world.loans) :
    binding.authority.Recorded world.loans :=
  Authority.Recorded.of_guarded_fold (Authority.Recorded.of_lend recorded)

/-- A property of the actual reachable resource bindings, independent of
their view's access mode. It is derived from ResourcesAccessible, never a
second inventory or a permission for an unrecorded authority. -/
def Value.ResourcesRecorded (world : World) (value : Value) : Prop :=
  ∀ resident authority access, value.ReachableResident world .owner .shared resident authority access →
    ∀ binding ∈ resident.resources, binding.authority.Recorded world.loans

theorem Value.ResourcesAccessible.resourcesRecorded {program : RuntimeProgram} {world : World} {value : Value} {access : Access}
    (ready : value.ResourcesAccessible program world access) : value.ResourcesRecorded world := by
  intro resident authority incoming reached binding member
  obtain ⟨current,requested,reached⟩ := reached.rebase .owner access
  exact (ready.2.2.2 resident current requested reached binding member).recorded.resourceView_backing

theorem Value.ResourcesRecorded.reachable {world : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (recorded : value.ResourcesRecorded world)
    (reached : value.ReachableResident world authority incoming resident current access) :
    resident.ResourcesRecorded world := by
  intro child next requested nested binding member
  obtain ⟨base,access,prior⟩ := reached.rebase .owner .shared
  obtain ⟨final,finalAccess,nested⟩ := nested.rebase base access
  exact recorded child final finalAccess (prior.trans nested) binding member

theorem Value.ReachableResident.recorded {world : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (resources : value.ResourcesRecorded world)
    (base : authority.Recorded world.loans)
    (reached : value.ReachableResident world authority incoming resident current access) :
    current.Recorded world.loans := by
  induction reached with
  | resident => exact base
  | referent _ _ found _ _ ih => exact ih.referenceView found _
  | resource prior member _ _ ih =>
      obtain ⟨current,access,prior⟩ := prior.rebase .owner .shared
      exact ih.resourceView (resources _ current access prior _ member) _

/-- Framing consults the permission projection of exactly the reference rows
observed by the actual pre-state graph. This includes absence; it never
manufactures a new edge. Custody/return administration is not a reference edge. -/
def Value.ReferenceRowsFramed (before after : World) (value : Value) : Prop :=
  ∀ identity current access, value.ReachableReference before .owner .shared identity current access →
    (after.loans.get identity).map Loan.permissionState = (before.loans.get identity).map Loan.permissionState

theorem Value.ReferenceRowsFramed.lookup {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity}
    (rows : value.ReferenceRowsFramed before after)
    (reached : value.ReachableReference before authority incoming identity current access) :
    (after.loans.get identity).map Loan.permissionState = (before.loans.get identity).map Loan.permissionState := by
  obtain ⟨current,access,reached⟩ := reached.rebase .owner .shared
  exact rows identity current access reached

theorem Value.ReferenceRowsFramed.selected {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity} {loan : Loan}
    (rows : value.ReferenceRowsFramed before after)
    (reached : value.ReachableReference before authority incoming identity current access)
    (found : before.loans.get identity = some loan) :
    ∃ changed, after.loans.get identity = some changed ∧ changed.permissionState = loan.permissionState := by
  have same := rows.lookup reached
  rw [found] at same
  exact Option.map_eq_some_iff.mp same

theorem Value.ReferenceRowsFramed.selected_before {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity} {loan : Loan}
    (rows : value.ReferenceRowsFramed before after)
    (reached : value.ReachableReference before authority incoming identity current access)
    (found : after.loans.get identity = some loan) :
    ∃ original, before.loans.get identity = some original ∧ loan.permissionState = original.permissionState := by
  have same := (rows.lookup reached).symm
  rw [found] at same
  obtain ⟨original,selected,equal⟩ := Option.map_eq_some_iff.mp same
  exact ⟨original,selected,equal.symm⟩

theorem Value.ReferenceRowsFramed.reachable {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (rows : value.ReferenceRowsFramed before after)
    (reached : value.ReachableResident before authority incoming resident current access) :
    resident.ReferenceRowsFramed before after := by
  intro identity next requested reference
  obtain ⟨base,access,prior⟩ := reached.rebase .owner .shared
  obtain ⟨final,access,carrier,nested,head⟩ := reference.rebase base access
  exact rows identity final access ⟨carrier,prior.trans nested,head⟩

/-- Custody is framed only for bindings actually retained in this resident's
reachable graph. An invocation may transfer an unrelated binding's custody. -/
def Value.HeldResourcesFramed (before after : World) (value : Value) : Prop :=
  ∀ resident authority access, value.ReachableResident before .owner .shared resident authority access →
    ∀ binding ∈ resident.resources, binding.HeldBy before resident.owner → binding.HeldBy after resident.owner

theorem Value.HeldResourcesFramed.reachable {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (held : value.HeldResourcesFramed before after)
    (reached : value.ReachableResident before authority incoming resident current access) :
    resident.HeldResourcesFramed before after := by
  intro child next requested nested binding member ready
  obtain ⟨base,access,prior⟩ := reached.rebase .owner .shared
  obtain ⟨final,finalAccess,nested⟩ := nested.rebase base access
  exact held child final finalAccess (prior.trans nested) binding member ready

/-- The authoritative compatibility product of one real resource batch, read
through the same pre-state reachable graph that observed it. The permission
projection of every observed reference row is retained; every observed retained
binding keeps its custody and its allocation-claim status. Custody and the
latest-owning-node law are separate fields because `Loan.permissionState`
erases both. -/
structure Value.BatchCompatible (before after : World) (value : Value) : Prop where
  rows : value.ReferenceRowsFramed before after
  custody : value.HeldResourcesFramed before after

theorem Value.BatchCompatible.reachable {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (batch : value.BatchCompatible before after)
    (reached : value.ReachableResident before authority incoming resident current access) :
    resident.BatchCompatible before after :=
  ⟨batch.rows.reachable reached,batch.custody.reachable reached⟩

/-- Both directions use the same pre-state support and observed rows.
Backward traversal recovers the prior node before consulting its outgoing
edge. The unchanged-loan-table case below is only a wrapper around this walk. -/
theorem Value.ReachableResident.frame_observed {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (rows : value.ReferenceRowsFramed before after)
    (framed : value.SupportFramed before after) :
    value.ReachableResident before authority incoming resident current access ↔
      value.ReachableResident after authority incoming resident current access := by
  constructor
  · intro reached
    induction reached with
    | resident located => exact .resident located
    | @referent carrier parent parentAuthority parentAccess loan target path resident prior reference found stored located ih =>
        have preserved := (framed loan.referent (Value.Support.reference ⟨carrier,prior,reference⟩ found)).1
        have nextStored : after.Stores loan.referent target := preserved.trans stored
        obtain ⟨changed,nextFound,shape⟩ := rows.selected ⟨carrier,prior,reference⟩ found
        have referent := (Loan.permissionState_eq_iff.mp shape).2.2.1
        have mode := (Loan.permissionState_eq_iff.mp shape).2.2.2.1
        simpa only [mode] using
          Value.ReachableResident.referent ih reference nextFound (referent ▸ nextStored) located
    | resource prior member stored located ih =>
        have preserved := (framed _ (Value.Support.resource prior member)).1
        exact Value.ReachableResident.resource ih member (preserved.trans stored) located
  · intro reached
    induction reached with
    | resident located => exact .resident located
    | @referent carrier parent parentAuthority parentAccess loan target path resident prior reference found stored located ih =>
        obtain ⟨original,oldFound,shape⟩ := rows.selected_before ⟨carrier,ih,reference⟩ found
        have referent := (Loan.permissionState_eq_iff.mp shape).2.2.1
        have mode := (Loan.permissionState_eq_iff.mp shape).2.2.2.1
        have preserved := (framed original.referent (Value.Support.reference ⟨carrier,ih,reference⟩ oldFound)).1
        have oldStored : before.Stores original.referent target := preserved.symm.trans (referent ▸ stored)
        simpa only [mode] using
          Value.ReachableResident.referent ih reference oldFound oldStored located
    | resource _ member stored located ih =>
        have preserved := (framed _ (Value.Support.resource ih member)).1
        exact Value.ReachableResident.resource ih member (preserved.symm.trans stored) located

theorem Value.ReachableResident.frame_batch {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (batch : value.BatchCompatible before after)
    (framed : value.SupportFramed before after) :
    value.ReachableResident before authority incoming resident current access ↔
      value.ReachableResident after authority incoming resident current access :=
  Value.ReachableResident.frame_observed batch.rows framed

theorem Value.ReachableResident.frame {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after) :
    value.ReachableResident before authority incoming resident current access ↔
      value.ReachableResident after authority incoming resident current access :=
  Value.ReachableResident.frame_observed (by intro identity current access reached; rw [loans])
    framed

theorem Value.ReachableReference.frame_observed {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity}
    (rows : value.ReferenceRowsFramed before after)
    (framed : value.SupportFramed before after) :
    value.ReachableReference before authority incoming identity current access ↔
      value.ReachableReference after authority incoming identity current access := by
  constructor
  · rintro ⟨resident,reached,reference⟩
    exact ⟨resident,(Value.ReachableResident.frame_observed rows framed).mp reached,reference⟩
  · rintro ⟨resident,reached,reference⟩
    exact ⟨resident,(Value.ReachableResident.frame_observed rows framed).mpr reached,reference⟩

theorem Value.ReachableReference.frame_batch {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity}
    (batch : value.BatchCompatible before after)
    (framed : value.SupportFramed before after) :
    value.ReachableReference before authority incoming identity current access ↔
      value.ReachableReference after authority incoming identity current access :=
  Value.ReachableReference.frame_observed batch.rows framed

theorem Value.ReachableReference.frame {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity}
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after) :
    value.ReachableReference before authority incoming identity current access ↔
      value.ReachableReference after authority incoming identity current access :=
  Value.ReachableReference.frame_observed (by intro identity current access reached; rw [loans])
    framed

theorem Value.Support.frame_observed {before after : World} {value : Value} {address : Address}
    (rows : value.ReferenceRowsFramed before after)
    (framed : value.SupportFramed before after) :
    value.Support before address ↔ value.Support after address := by
  constructor
  · rintro ⟨resident,authority,access,reached,edge⟩
    refine ⟨resident,authority,access,(Value.ReachableResident.frame_observed rows framed).mp reached,?_⟩
    rcases edge with ⟨identity,loan,head,found,equal⟩ | resource
    · obtain ⟨changed,selected,shape⟩ := rows.selected ⟨resident,reached,head⟩ found
      exact Or.inl ⟨identity,changed,head,selected,(Loan.permissionState_eq_iff.mp shape).2.2.1.trans equal⟩
    · exact Or.inr resource
  · rintro ⟨resident,authority,access,reached,edge⟩
    have prior := (Value.ReachableResident.frame_observed rows framed).mpr reached
    refine ⟨resident,authority,access,prior,?_⟩
    rcases edge with ⟨identity,loan,head,found,equal⟩ | resource
    · obtain ⟨original,selected,shape⟩ := rows.selected_before ⟨resident,prior,head⟩ found
      exact Or.inl ⟨identity,original,head,selected,(Loan.permissionState_eq_iff.mp shape).2.2.1.symm.trans equal⟩
    · exact Or.inr resource

theorem Value.Support.frame_batch {before after : World} {value : Value} {address : Address}
    (batch : value.BatchCompatible before after)
    (framed : value.SupportFramed before after) :
    value.Support before address ↔ value.Support after address :=
  Value.Support.frame_observed batch.rows framed

theorem Value.Support.frame {before after : World} {value : Value} {address : Address}
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after) :
    value.Support before address ↔ value.Support after address :=
  Value.Support.frame_observed (by intro identity current access reached; rw [loans])
    framed

theorem Authority.Custodied.same_loans {before after : World} {authority : Authority} {custody : ClaimCustody}
    (loans : after.loans = before.loans) (held : authority.Custodied before custody) :
    authority.Custodied after custody := by
  induction authority with
  | owner => trivial
  | loan identity => simpa only [Authority.Custodied,loans] using held
  | shared backing => simpa only [Authority.Custodied,loans] using held
  | guarded backing carrier ih => exact ih held

theorem AllocationClaim.frame {before after : World} {authority : Authority} {address : Address}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (claim : AllocationClaim before authority address) :
    AllocationClaim after authority address := by
  obtain ⟨identity,loan,root,domain,parent,found,live,kind,referent,whole,selected,home,latest⟩ := claim
  obtain ⟨changed,newSelected,same⟩ := locations.root selected
  have homeEq : changed.home = root.home := by simpa only [Root.location] using congrArg Root.home same
  refine ⟨identity,loan,changed,domain,parent,by simpa only [loans] using found,live,kind,referent,whole,
    newSelected,by simpa only [homeEq] using home,?_⟩
  intro child successor found live kind ancestry
  exact latest child successor (by simpa only [loans] using found) live kind (ancestry.transport loans.symm)

theorem StorageBinding.HeldBy.referent_recorded {world : World} {owner : Identity} {binding : StorageBinding}
    (held : binding.HeldBy world owner) :
    ∃ identity loan, world.loans.get identity = some loan ∧ loan.live = true ∧ loan.referent = binding.address := by
  obtain ⟨custody,resources⟩ := held
  rcases resources with ⟨claim,_⟩ | borrow
  · obtain ⟨identity,loan,root,domain,parent,found,live,kind,referent,whole,selected,home,latest⟩ := claim
    exact ⟨identity,loan,found,live,referent⟩
  · obtain ⟨identity,loan,parent,found,live,kind,referent,shared⟩ := borrow
    exact ⟨identity,loan,found,live,referent⟩

/-- Closed resources and restored references bound the entire retained
support, even when a reference view is frozen and cannot currently be used. -/
theorem Value.Support.root_bound {program : RuntimeProgram} {world : World} {value : Value} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) (closed : value.ResourcesClosed program world) (restored : value.LoansRestored program world)
    {address : Address} (supported : value.Support world address) : address.root < world.nextRoot := by
  obtain ⟨resident,authority,access,reached,edge⟩ := supported
  rcases edge with ⟨identity,loan,head,found,referent⟩ | ⟨binding,member,referent⟩
  · obtain ⟨actual,selected,live,_⟩ := restored identity authority access ⟨resident,reached,head⟩
    have same : loan = actual := Option.some.inj (found.symm.trans selected)
    subst actual
    simpa only [referent] using World.live_loan_root_bound valid found live
  · obtain ⟨identity,loan,found,live,target⟩ := ((closed resident authority access reached).1 binding member).referent_recorded
    simpa only [target,referent] using World.live_loan_root_bound valid found live



/-- Closed resources and restored references cannot observe storage with no
incoming live loans. This support fact is shared by handoff and cleanup. -/
theorem Value.Support.avoids_private {program : RuntimeProgram} {world : World}
    {value : Value} {address observed : Address}
    (closed : value.ResourcesClosed program world) (restored : value.LoansRestored program world)
    (privateRoot : CanEndStorage world address.root) (supported : value.Support world observed) :
    ¬ address.Overlaps observed := by
  intro overlap
  obtain ⟨resident,current,requested,reached,edge⟩ := supported
  rcases edge with ⟨identity,loan,head,found,rfl⟩ | ⟨binding,member,rfl⟩
  · obtain ⟨active,selected,live,_⟩ := restored identity current requested ⟨resident,reached,head⟩
    have same := Option.some.inj (selected.symm.trans found)
    exact privateRoot.1 identity loan found (same ▸ live) overlap.1.symm
  · obtain ⟨identity,loan,found,live,referent⟩ :=
      StorageBinding.HeldBy.referent_recorded ((closed resident current requested reached).1 binding member)
    exact privateRoot.1 identity loan found live ((congrArg Address.root referent).trans overlap.1.symm)

/-- A write outside the original support retains its actual reachable graph. -/
theorem Value.SupportFramed.of_write {before after : World} {address : Address} {replacement : Option Value}
    {value : Value}
    (written : before.write address replacement = some after)
    (outside : ∀ observed, value.Support before observed → ¬ address.Overlaps observed)
    (root : ∀ observed, value.Support before observed → (after.roots.get observed.root).map Root.location =
      (before.roots.get observed.root).map Root.location) :
    value.SupportFramed before after :=
  fun observed supported =>
    ⟨World.write_disjoint written (outside observed supported),root observed supported⟩


theorem StorageBinding.HeldBy.frame {before after : World} {binding : StorageBinding} {owner : Identity}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (held : binding.HeldBy before owner) : binding.HeldBy after owner := by
  refine ⟨held.1.same_loans loans,?_⟩
  rcases held.2 with ⟨claim,writable⟩ | storage
  · exact Or.inl ⟨claim.frame locations loans,writable⟩
  · exact Or.inr (by simpa only [loans] using storage)

theorem Value.ResourcesClosed.frame_scoped {program : RuntimeProgram} {before after : World} {value : Value}
    (rows : value.ReferenceRowsFramed before after)
    (framed : value.SupportFramed before after)
    (heldBy : value.HeldResourcesFramed before after)
    (closed : value.ResourcesClosed program before) : value.ResourcesClosed program after := by
  intro resident authority access reached
  have prior := (Value.ReachableResident.frame_observed rows framed).mpr reached
  obtain ⟨held,declared⟩ := closed resident authority access prior
  exact ⟨fun binding member => heldBy resident authority access prior binding member (held binding member),
    declared.framed (framed.reachable prior)⟩

theorem Value.ResourcesClosed.frame_observed {program : RuntimeProgram} {before after : World} {value : Value}
    (rows : value.ReferenceRowsFramed before after)
    (framed : value.SupportFramed before after)
    (heldBy : ∀ binding owner, StorageBinding.HeldBy before owner binding → binding.HeldBy after owner)
    (closed : value.ResourcesClosed program before) : value.ResourcesClosed program after :=
  closed.frame_scoped rows framed
    (fun resident _ _ _ binding _ held => heldBy binding resident.owner held)

theorem Value.ResourcesClosed.frame_batch {program : RuntimeProgram} {before after : World} {value : Value}
    (batch : value.BatchCompatible before after)
    (framed : value.SupportFramed before after)
    (closed : value.ResourcesClosed program before) : value.ResourcesClosed program after :=
  closed.frame_scoped batch.rows framed batch.custody

theorem Value.ResourcesClosed.frame {program : RuntimeProgram} {before after : World} {value : Value}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (closed : value.ResourcesClosed program before) : value.ResourcesClosed program after :=
  closed.frame_observed (by intro identity current access reached; rw [loans])
    framed (fun _ _ held => held.frame locations loans)

theorem Value.LoansRestored.frame_observed {program : RuntimeProgram} {before after : World} {value : Value}
    (rows : value.ReferenceRowsFramed before after)
    (framed : value.SupportFramed before after)
    (heldBy : ∀ binding owner, StorageBinding.HeldBy before owner binding → binding.HeldBy after owner)
    (restored : value.LoansRestored program before) : value.LoansRestored program after := by
  intro identity authority access reached
  have prior := (Value.ReachableReference.frame_observed rows framed).mpr reached
  obtain ⟨loan,found,live,⟨target,stored,initialized⟩,closed⟩ := restored identity authority access prior
  have preserved := (framed _ (Value.Support.reference prior found)).1
  obtain ⟨changed,selected,shape⟩ := rows.selected prior found
  have referent := (Loan.permissionState_eq_iff.mp shape).2.2.1
  have active := (Loan.permissionState_eq_iff.mp shape).2.2.2.2.2.1
  refine ⟨changed,selected,active.trans live,⟨target,by simpa only [referent,World.Stores] using preserved.trans stored,initialized⟩,?_⟩
  intro referent newStored
  have oldStored : before.Stores loan.referent referent := preserved.symm.trans
    (by simpa only [(Loan.permissionState_eq_iff.mp shape).2.2.1,World.Stores] using newStored)
  have nested := Value.ReachableResident.referent_prefix prior found oldStored (.resident (.root (value := referent)))
  exact (closed referent oldStored).frame_observed (rows.reachable nested) (framed.reachable nested) heldBy

theorem Value.LoansRestored.frame {program : RuntimeProgram} {before after : World} {value : Value}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (restored : value.LoansRestored program before) : value.LoansRestored program after :=
  restored.frame_observed (by intro identity current access reached; rw [loans])
    framed (fun _ _ held => held.frame locations loans)

theorem Value.ReferencesAccessible.frame_observed {before after : World} {value : Value}
    {authority : Authority} {incoming : Access}
    (rows : value.ReferenceRowsFramed before after)
    (framed : value.SupportFramed before after)
    (permitted : ∀ authority access address, Permitted before authority access address → Permitted after authority access address)
    (ready : value.ReferencesAccessible before authority incoming) : value.ReferencesAccessible after authority incoming := by
  intro identity current access reached
  have prior := (Value.ReachableReference.frame_observed rows framed).mpr reached
  obtain ⟨loan,found,live,permission⟩ := ready identity current access prior
  obtain ⟨changed,selected,shape⟩ := rows.selected prior found
  obtain ⟨_,_,referent,mode,_,active,_,_⟩ := Loan.permissionState_eq_iff.mp shape
  exact ⟨changed,selected,active.trans live,
    by simpa only [referent,mode] using permitted _ _ _ permission⟩

theorem Value.ReferencesAccessible.frame {before after : World} {value : Value}
    {authority : Authority} {incoming : Access}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (ready : value.ReferencesAccessible before authority incoming) : value.ReferencesAccessible after authority incoming :=
  ready.frame_observed (by intro identity current access reached; rw [loans])
    framed (fun _ _ _ permission => permission.locationExtension locations loans)

theorem Value.ResourcesAccessible.frame_observed {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access}
    (rows : value.ReferenceRowsFramed before after)
    (framed : value.SupportFramed before after)
    (heldBy : ∀ binding owner, StorageBinding.HeldBy before owner binding → binding.HeldBy after owner)
    (permitted : ∀ authority access address, Permitted before authority access address → Permitted after authority access address)
    (ready : value.ResourcesAccessible program before access) : value.ResourcesAccessible program after access := by
  refine ⟨ready.1.frame_observed rows framed heldBy,ready.2.1.frame_observed rows framed heldBy,
    ready.references.frame_observed rows framed permitted,?_⟩
  intro resident authority incoming reached binding member
  have permission := ready.2.2.2 resident authority incoming
    ((Value.ReachableResident.frame_observed rows framed).mpr reached) binding member
  exact permitted _ _ _ permission

theorem Value.ResourcesAccessible.frame {program : RuntimeProgram} {before after : World} {value : Value} {access : Access}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (ready : value.ResourcesAccessible program before access) : value.ResourcesAccessible program after access :=
  ready.frame_observed (by intro identity current access reached; rw [loans])
    framed (fun _ _ held => held.frame locations loans)
    (fun _ _ _ permission => permission.locationExtension locations loans)

theorem Value.HandoffReady.frame_observed {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access} {footprint : List Address}
    (rows : value.ReferenceRowsFramed before after)
    (framed : value.SupportFramed before after)
    (heldBy : ∀ binding owner, StorageBinding.HeldBy before owner binding → binding.HeldBy after owner)
    (permitted : ∀ authority access address, Permitted before authority access address → Permitted after authority access address)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint := by
  refine ⟨ready.1.frame_observed rows framed heldBy permitted,?_⟩
  intro source member observed supported
  exact ready.2 source member observed ((Value.Support.frame_observed rows framed).mpr supported)

theorem Value.HandoffReady.frame {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access} {footprint : List Address}
    (locations : before.LocationExtension after) (loans : after.loans = before.loans)
    (framed : value.SupportFramed before after)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint :=
  ready.frame_observed (by intro identity current access reached; rw [loans])
    framed (fun _ _ held => held.frame locations loans)
    (fun _ _ _ permission => permission.locationExtension locations loans)

theorem Value.LoansRestored.frame_batch {program : RuntimeProgram} {before after : World} {value : Value}
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (restored : value.LoansRestored program before) : value.LoansRestored program after := by
  intro identity authority access reached
  have prior := (Value.ReachableReference.frame_batch (authority := .owner) batch framed).mpr reached
  obtain ⟨loan,found,live,⟨target,stored,initialized⟩,closed⟩ := restored identity authority access prior
  have preserved := (framed _ (Value.Support.reference prior found)).1
  obtain ⟨changed,selected,shape⟩ := batch.rows.selected prior found
  have referent := (Loan.permissionState_eq_iff.mp shape).2.2.1
  have active := (Loan.permissionState_eq_iff.mp shape).2.2.2.2.2.1
  refine ⟨changed,selected,active.trans live,
    ⟨target,by simpa only [referent,World.Stores] using preserved.trans stored,initialized⟩,?_⟩
  intro storedValue newStored
  have oldStored : before.Stores loan.referent storedValue := preserved.symm.trans
    (by simpa only [referent,World.Stores] using newStored)
  have nested := Value.ReachableResident.referent_prefix prior found oldStored (.resident (.root (value := storedValue)))
  exact (closed storedValue oldStored).frame_batch (batch.reachable nested) (framed.reachable nested)

/-- The observed graph carries a mutation to readiness. `permitted` ranges over
every recorded authority, which is exactly what a pure frame (unchanged loan
table) discharges. A step that inserts a row the source table never held cannot
satisfy it, because that row may overlap an address the graph already reads;
such a step must restrict the obligation to the views the graph actually
observes. -/
theorem Value.ReferencesAccessible.frame_batch {before after : World} {value : Value}
    {authority : Authority} {incoming : Access}
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : ∀ (authority : Authority) (access : Access) (address : Address),
      authority.Recorded before.loans →
      Permitted before authority access address → Permitted after authority access address)
    (ready : value.ReferencesAccessible before authority incoming) :
    value.ReferencesAccessible after authority incoming := by
  intro identity current access reached
  have prior := (Value.ReachableReference.frame_batch batch framed).mpr reached
  obtain ⟨loan,found,live,permission⟩ := ready identity current access prior
  obtain ⟨changed,selected,shape⟩ := batch.rows.selected prior found
  obtain ⟨_,_,referent,mode,_,active,_,_⟩ := Loan.permissionState_eq_iff.mp shape
  refine ⟨changed,selected,active.trans live,?_⟩
  have stated := permitted (current.referenceView identity (ReferenceAccess access loan.mode))
    (ReferenceAccess access loan.mode) loan.referent permission.recorded permission
  simpa only [referent,mode] using stated

theorem Value.ResourcesAccessible.frame_batch {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access}
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : ∀ (authority : Authority) (access : Access) (address : Address),
      authority.Recorded before.loans →
      Permitted before authority access address → Permitted after authority access address)
    (ready : value.ResourcesAccessible program before access) : value.ResourcesAccessible program after access := by
  refine ⟨ready.1.frame_batch batch framed,ready.2.1.frame_batch batch framed,
    ready.references.frame_batch batch framed permitted,?_⟩
  intro resident authority incoming reached binding member
  have prior :=
    (Value.ReachableResident.frame_batch (authority := .owner) batch framed).mpr reached
  have permission := ready.2.2.2 resident authority incoming prior binding member
  exact permitted (authority.resourceView binding incoming) (ResourceAccess incoming binding)
    binding.address permission.recorded permission

theorem Value.HandoffReady.frame_batch {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access} {footprint : List Address}
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : ∀ (authority : Authority) (access : Access) (address : Address),
      authority.Recorded before.loans →
      Permitted before authority access address → Permitted after authority access address)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint :=
  ⟨ready.1.frame_batch batch framed permitted,
    fun source member observed supported =>
      ready.2 source member observed ((Value.Support.frame_batch batch framed).mpr supported)⟩

/-- The row-level laws one real resource mutation supplies. `permissions` is the
retained-row permission projection, `claims` is the allocation-claim frame and
revocation read at the observer's own authority, and `custody` is the actual
administrative change of a custodian. All three are stated on the real loan
table, below the reachable graph, so a fresh row, a custody move and a
revocation are visible in exactly one place. -/
structure World.ResourceRowsRetained (before after : World) : Prop where
  permissions : ∀ identity loan, before.loans.get identity = some loan →
    ∃ current, after.loans.get identity = some current ∧ current.permissionState = loan.permissionState
  claims : ∀ (authority : Authority) (address : Address),
    AllocationClaim before authority address → AllocationClaim after authority address
  custody : ∀ (authority : Authority) (custody : ClaimCustody),
    authority.Custodied before custody → authority.Custodied after custody

/-- The observed resource graph carries those row laws to every retained binding
of every reachable resident. A mutation that moves a custodian away from its
`.resident` owner supplies no `custody` law for that owner, and a fresh live
owning child supplies no `claims` law for the claim it supersedes: both are real
revocations, never framing gaps. -/
theorem Value.HeldResourcesFramed.of_rows {before after : World} {value : Value}
    (rows : before.ResourceRowsRetained after) : value.HeldResourcesFramed before after := by
  intro resident authority access reached binding member held
  obtain ⟨custodied,resource⟩ := held
  refine ⟨rows.custody _ _ custodied,?_⟩
  rcases resource with ⟨claim,readonly⟩ | ⟨identity,loan,parented,found,live,kind,referent,readonly⟩
  · exact Or.inl ⟨rows.claims _ _ claim,readonly⟩
  · obtain ⟨current,currentFound,shape⟩ := rows.permissions identity loan found
    obtain ⟨_,_,referentEq,modeEq,_,liveEq,kindEq,_⟩ := Loan.permissionState_eq_iff.mp shape
    exact Or.inr ⟨identity,current,parented,currentFound,liveEq.trans live,kindEq.trans kind,
      referentEq.trans referent,fun read => modeEq.trans (readonly read)⟩

/-- The retained-row permission projection already fixes every observed
reference row, provided the observer supplies the row existence that its own
`ReferencesAccessible` readiness establishes. This is the bridge from a rule's
row package to the observed reference frame, with no second graph walk. -/
theorem Value.ReferenceRowsFramed.of_rows {before after : World} {value : Value}
    (rows : before.ResourceRowsRetained after)
    (references : ∀ identity current access,
      value.ReachableReference before .owner .shared identity current access →
        ∃ loan, before.loans.get identity = some loan) :
    value.ReferenceRowsFramed before after := by
  intro identity current access reached
  obtain ⟨loan,found⟩ := references identity current access reached
  obtain ⟨current,currentFound,shape⟩ := rows.permissions identity loan found
  rw [currentFound,found,Option.map_some,Option.map_some,shape]

/-- The whole graph-level product of one real mutation, from its row package and
the row existence its observed readiness already carries. -/
theorem Value.BatchCompatible.of_rows {before after : World} {value : Value}
    (rows : before.ResourceRowsRetained after)
    (references : ∀ identity current access,
      value.ReachableReference before .owner .shared identity current access →
        ∃ loan, before.loans.get identity = some loan) :
    value.BatchCompatible before after :=
  ⟨Value.ReferenceRowsFramed.of_rows rows references,
   Value.HeldResourcesFramed.of_rows rows⟩

/-- One retained binding is retained by the row package alone; consumers use
this to discharge the `heldBy` obligation of the observed-graph frame from an
actual producer's rows, with no second walk and no anchor side condition. -/
theorem StorageBinding.HeldBy.of_rows {before after : World} {binding : StorageBinding} {owner : Identity}
    (rows : before.ResourceRowsRetained after) (held : binding.HeldBy before owner) :
    binding.HeldBy after owner :=
  ⟨rows.custody _ _ held.1,by
    rcases held.2 with ⟨claim,writable⟩ | storage
    · exact Or.inl ⟨rows.claims _ _ claim,writable⟩
    · obtain ⟨identity,loan,parented,found,live,kind,referent,shared⟩ := storage
      obtain ⟨current,currentFound,shape⟩ := rows.permissions identity loan found
      obtain ⟨_,_,referentEq,modeEq,_,liveEq,kindEq,_⟩ := Loan.permissionState_eq_iff.mp shape
      exact Or.inr ⟨identity,current,parented,currentFound,liveEq.trans live,kindEq.trans kind,
        referentEq.trans referent,fun read => modeEq.trans (shared read)⟩⟩

/-- One recorded row changes only its administrative custody fields. The
parent link, referent geometry and liveness are retained, so the ancestry
relation is unchanged step for step. -/
theorem AncestorLoan.of_custody_update {before after : World} {identity : Identity} {original : Loan}
    {newCustody : ClaimCustody} {requested : Bool}
    (found : before.loans.get identity = some original)
    (rows : after.loans = before.loans.set identity
      { original with custody := some newCustody, returnRequested := requested })
    {ancestor descendant : Identity} (related : AncestorLoan after ancestor descendant) :
    AncestorLoan before ancestor descendant := by
  induction related with
  | refl => exact .refl
  | @parent parent child loan' childFound link prior ih =>
      by_cases same : child = identity
      · subst same
        have sameRow : loan' = { original with custody := some newCustody, returnRequested := requested } :=
          Option.some.inj (childFound.symm.trans (by rw [rows,Table.get_set]))
        refine .parent found ?_ ih
        have link' := sameRow ▸ link
        simpa using link'
      · have retained : before.loans.get child = some loan' := by
          rw [rows,Table.get_set_other _ _ _ _ same] at childFound
          exact childFound
        exact .parent retained link ih

/-- A row that changes only custody keeps its referent, liveness, kind and
parent, so it keeps being the latest live owning node for its allocation. -/
theorem AllocationClaim.of_custody_update {before after : World} {authority : Authority} {address : Address}
    {identity : Identity} {original : Loan} {newCustody : ClaimCustody} {requested : Bool}
    (locations : before.LocationExtension after)
    (found : before.loans.get identity = some original)
    (rows : after.loans = before.loans.set identity
      { original with custody := some newCustody, returnRequested := requested })
    (claim : AllocationClaim before authority address) : AllocationClaim after authority address := by
  obtain ⟨claimId,claimLoan,root,domain,parent,claimFound,live,owning,referent,whole,selected,home,latest⟩ := claim
  obtain ⟨changed,nextSelected,same⟩ := locations.root selected
  have homeEq : changed.home = root.home := by simpa only [Root.location] using congrArg Root.home same
  have retained : ∀ {child : Identity} {successor : Loan}, after.loans.get child = some successor →
      child ≠ identity → before.loans.get child = some successor := by
    intro child successor childFound different
    rw [rows,Table.get_set_other _ _ _ _ different] at childFound
    exact childFound
  have moved : ∀ {successor : Loan}, after.loans.get identity = some successor →
      successor = { original with custody := some newCustody, returnRequested := requested } := by
    intro successor successorFound
    exact Option.some.inj (successorFound.symm.trans (by rw [rows,Table.get_set]))
  have latestAfter : ∀ child successor, after.loans.get child = some successor → successor.live = true →
      successor.kind = .owning → AncestorLoan after claimId child → child = claimId := by
    intro child successor childFound childLive childOwning ancestry
    have ancestryBefore := ancestry.of_custody_update found rows
    by_cases childSame : child = identity
    · subst childSame
      have rowEq := moved childFound
      exact latest child original found (by simpa [rowEq] using childLive)
        (by simpa [rowEq] using childOwning) ancestryBefore
    · exact latest child successor (retained childFound childSame) childLive childOwning ancestryBefore
  by_cases sameId : claimId = identity
  · subst sameId
    have sameRow : claimLoan = original := Option.some.inj (claimFound.symm.trans found)
    exact ⟨claimId,{ original with custody := some newCustody, returnRequested := requested },changed,domain,
      parent,by rw [rows,Table.get_set],by simpa [sameRow] using live,by simpa [sameRow] using owning,
      by simpa [sameRow] using referent,whole,nextSelected,by simpa only [homeEq] using home,latestAfter⟩
  · have rowFound : after.loans.get claimId = some claimLoan := by
      rw [rows,Table.get_set_other _ _ _ _ sameId]
      exact claimFound
    exact ⟨claimId,claimLoan,changed,domain,parent,rowFound,live,owning,referent,whole,nextSelected,
      by simpa only [homeEq] using home,latestAfter⟩

/-- Custody administration of one recorded row is retained for every custodian
that still holds it: the row's kind may make custody irrelevant, the new
custodian may be that same custodian, or the observer's own row is elsewhere. -/
theorem Authority.Custodied.of_row_change {before after : World} {authority : Authority} {c : ClaimCustody}
    {identity : Identity} {replacement : Loan}
    (rows : after.loans = before.loans.set identity replacement)
    (irrelevant : authority.parentLoan = some identity →
      replacement.kind = .restoring ∨ replacement.kind = .destructor ∨
        replacement.custody = some c)
    (held : authority.Custodied before c) : authority.Custodied after c := by
  induction authority with
  | owner => trivial
  | loan id =>
      obtain ⟨current,currentFound,allowed⟩ := held
      by_cases same : id = identity
      · subst same
        exact ⟨replacement,by rw [rows,Table.get_set],irrelevant rfl⟩
      · exact ⟨current,by rw [rows,Table.get_set_other _ _ _ _ same]; exact currentFound,allowed⟩
  | shared backing ih =>
      exact Authority.Recorded.transport held (fun id loan found' => by
        by_cases same : id = identity
        · subst same
          exact ⟨replacement,by rw [rows,Table.get_set]⟩
        · exact ⟨loan,by rw [rows,Table.get_set_other _ _ _ _ same]; exact found'⟩)
  | guarded backing carrier ih => exact ih irrelevant held

theorem Authority.Custodied.of_custody_update {before after : World} {authority : Authority} {c : ClaimCustody}
    {identity : Identity} {original : Loan} {newCustody : ClaimCustody} {requested : Bool}
    (rows : after.loans = before.loans.set identity
      { original with custody := some newCustody, returnRequested := requested })
    (kept : authority.parentLoan ≠ some identity ∨ original.kind = .restoring ∨
      original.kind = .destructor ∨ newCustody = c)
    (held : authority.Custodied before c) : authority.Custodied after c := by
  refine Authority.Custodied.of_row_change rows ?_ held
  intro parent
  rcases kept with kept | kept | kept | kept
  · exact absurd parent kept
  · exact Or.inl kept
  · exact Or.inr (Or.inl kept)
  · exact Or.inr (Or.inr (by rw [kept]))

theorem Value.ReferenceRowsFramed.of_custody_update {before after : World} {value : Value}
    {identity : Identity} {original : Loan} {newCustody : ClaimCustody} {requested : Bool}
    (found : before.loans.get identity = some original)
    (rows : after.loans = before.loans.set identity
      { original with custody := some newCustody, returnRequested := requested }) :
    value.ReferenceRowsFramed before after := by
  intro observed current access reached
  by_cases same : observed = identity
  · subst same
    simp only [rows,Table.get_set,Option.map_some,found,Loan.permissionState]
  · rw [rows,Table.get_set_other _ _ _ _ same]

/-- The observed resource graph keeps every retained binding when one recorded
row changes only its administrative custody fields, except for the bindings
whose own custodian row is that row and whose new custodian is somebody else.
That exception is the real transfer of custody, never a framing gap. -/
theorem Value.HeldResourcesFramed.of_custody_update {before after : World} {value : Value}
    {identity : Identity} {original : Loan} {newCustody : ClaimCustody} {requested : Bool}
    (locations : before.LocationExtension after)
    (found : before.loans.get identity = some original)
    (rows : after.loans = before.loans.set identity
      { original with custody := some newCustody, returnRequested := requested })
    (applied : original.kind = .restoring ∨ original.kind = .destructor ∨
      ∀ resident authority access, value.ReachableResident before .owner .shared resident authority access →
        ∀ binding ∈ resident.resources, binding.authority.parentLoan ≠ some identity) :
    value.HeldResourcesFramed before after := by
  intro resident authority access reached binding member held
  obtain ⟨custodied,resource⟩ := held
  have keep : binding.authority.parentLoan ≠ some identity ∨ original.kind = .restoring ∨
      original.kind = .destructor ∨ newCustody = .resident resident.owner := by
    rcases applied with applied | applied
    · exact Or.inr (Or.inl applied)
    · rcases applied with applied | applied
      · exact Or.inr (Or.inr (Or.inl applied))
      · exact Or.inl (applied resident authority access reached binding member)
  refine ⟨Authority.Custodied.of_custody_update rows keep custodied,?_⟩
  rcases resource with ⟨claim,readonly⟩ | ⟨claimId,loan,parented,claimFound,live,kind,referent,readonly⟩
  · exact Or.inl ⟨claim.of_custody_update locations found rows,readonly⟩
  · by_cases same : claimId = identity
    · subst same
      have sameRow : loan = original := Option.some.inj (claimFound.symm.trans found)
      have rowFound : after.loans.get claimId = some
          { loan with custody := some newCustody, returnRequested := requested } := by
        rw [rows,Table.get_set]
        exact congrArg some (by rw [sameRow])
      exact Or.inr ⟨claimId,{ loan with custody := some newCustody, returnRequested := requested },
        parented,rowFound,by simpa using live,by simpa using kind,by simpa using referent,
        readonly⟩
    · have rowFound : after.loans.get claimId = some loan := by
        rw [rows,Table.get_set_other _ _ _ _ same]
        exact claimFound
      exact Or.inr ⟨claimId,loan,parented,rowFound,live,kind,referent,readonly⟩

/-- The whole compatibility product for one custody-administrative row change. -/
theorem Value.BatchCompatible.of_custody_update {before after : World} {value : Value}
    {identity : Identity} {original : Loan} {newCustody : ClaimCustody} {requested : Bool}
    (locations : before.LocationExtension after)
    (found : before.loans.get identity = some original)
    (rows : after.loans = before.loans.set identity
      { original with custody := some newCustody, returnRequested := requested })
    (applied : original.kind = .restoring ∨ original.kind = .destructor ∨
      ∀ resident authority access, value.ReachableResident before .owner .shared resident authority access →
        ∀ binding ∈ resident.resources, binding.authority.parentLoan ≠ some identity) :
    value.BatchCompatible before after :=
  ⟨Value.ReferenceRowsFramed.of_custody_update found rows,
   Value.HeldResourcesFramed.of_custody_update locations found rows applied⟩

theorem Transfers.moveReady {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {value : Value}
    (moved : Transfers program before authority source destination after) (stored : before.Stores source value) :
    value.MoveReady program before [source,destination] := by
  cases moved with
  | move selected _ ready _ _ _ _ _ _ =>
      have same := Option.some.inj (stored.symm.trans selected)
      subst same
      exact ready

theorem Transfers.supportFramed {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {value : Value}
    (moved : Transfers program before authority source destination after) (stored : before.Stores source value) :
    value.SupportFramed before after := by
  have ready := moved.moveReady stored
  have locations := moved.locations
  obtain ⟨cleared,clear,install⟩ := move_preserves_owner stored moved
  intro observed supported
  have sourceOutside := ready.2 source (by simp) observed supported
  have destinationOutside := ready.2 destination (by simp) observed supported
  exact ⟨(World.write_disjoint install destinationOutside).trans (World.write_disjoint clear sourceOutside),locations _⟩

/-- This is the actual graph-local frame consumed by matching transported
payloads, including references stored behind nominal raw-resource carriers. -/
theorem Transfers.reachable_reference_framed {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {value : Value}
    (moved : Transfers program before authority source destination after) (stored : before.Stores source value)
    {identity : Identity} {current : Authority} {access : Access}
    (reached : value.ReachableReference before .owner .shared identity current access)
    {loan : Loan} (found : before.loans.get identity = some loan) :
    after.loans.get identity = some loan ∧
      ∀ target, before.Stores loan.referent target → after.Stores loan.referent target := by
  have preserved := ((moved.supportFramed stored) _ (Value.Support.reference reached found)).1
  exact ⟨by simpa only [moved.loans] using found,fun _ selected => preserved.trans selected⟩

theorem Transfers.handed_off_ready {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {value : Value}
    (moved : Transfers program before authority source destination after) (stored : before.Stores source value) :
    after.Stores destination value ∧ value.Initialized ∧ value.ResourcesAccessible program after .owned := by
  have ready := moved.moveReady stored
  have framed := moved.supportFramed stored
  have preserved := ready.1.frame (.of_locations moved.locations) moved.loans framed
  cases moved with
  | move selected initialized _ _ _ _ _ _ install =>
      have same := Option.some.inj (stored.symm.trans selected)
      subst same
      have installed := World.write_read_inside install []
      simp only [List.append_nil] at installed
      change after.Stores destination value at installed
      exact ⟨installed,initialized,preserved⟩


/-- Clearing private storage preserves restoration at every disjoint referent;
closed resources and restored references supply the required support exclusion. -/
theorem World.ResourcesClosed.private_write {program : RuntimeProgram} {before after : World}
    {address mutation : Address} {replacement : Option Value}
    (closed : before.ResourcesClosed program address) (safe : CanEndStorage before mutation.root)
    (outside : ¬ mutation.Overlaps address) (written : before.write mutation replacement = some after) :
    after.ResourcesClosed program address := by
  intro value stored
  obtain ⟨resources,restored⟩ := closed value ((World.write_disjoint written outside).symm.trans stored)
  have framed : value.SupportFramed before after := Value.SupportFramed.of_write written
    (fun _ supported => supported.avoids_private resources restored safe)
    (fun observed _ => World.write_locations written observed.root)
  have locations := World.LocationExtension.of_locations (World.write_locations written)
  exact ⟨resources.frame locations (World.write_loans written) framed,
    restored.frame locations (World.write_loans written) framed⟩


/-! ## Exact residuals retain the common semantic graph -/

/-- Pruning can remove structural residents, not invent reference or erased
resource edges. Every surviving structural node keeps its exact residual;
nodes reached through retained storage are unchanged. -/
theorem Value.AfterClearing.reachable {world : World} {original current resident : Value}
    {address : Address} {cleared : List Address} {authority final : Authority} {incoming access : Access}
    (pruned : original.AfterClearing address cleared current)
    (reached : current.ReachableResident world authority incoming resident final access) :
    ∃ prior, original.ReachableResident world authority incoming prior final access ∧ resident.shell = prior.shell ∧
      (resident = prior ∨ ∃ path, ResidentAt original path prior ∧
        prior.AfterClearing { address with fields := address.fields ++ path } cleared resident) := by
  induction reached with
  | resident located =>
      obtain ⟨prior,atPrior,shape,residual⟩ := pruned.nested located
      exact ⟨prior,.resident atPrior,shape,Or.inr ⟨_,atPrior,residual⟩⟩
  | referent _ head found stored located ih =>
      obtain ⟨prior,reached,shape,_⟩ := ih
      have heads := congrArg Value.head shape
      simp only [Value.shell,Value.withFields,Value.head] at heads
      exact ⟨_,.referent reached (heads.symm.trans head) found stored located,rfl,Or.inl rfl⟩
  | resource _ member stored located ih =>
      obtain ⟨prior,reached,shape,_⟩ := ih
      have resources := congrArg Value.resources shape
      change _ = prior.resources at resources
      exact ⟨_,.resource reached (resources ▸ member) stored located,rfl,Or.inl rfl⟩

theorem Value.AfterClearing.references {world : World} {original current : Value}
    {address : Address} {cleared : List Address} {authority final : Authority} {incoming access : Access} {identity : Identity}
    (pruned : original.AfterClearing address cleared current)
    (reached : current.ReachableReference world authority incoming identity final access) :
    original.ReachableReference world authority incoming identity final access := by
  obtain ⟨resident,reached,head⟩ := reached
  obtain ⟨prior,reached,shape,_⟩ := pruned.reachable reached
  have heads := congrArg Value.head shape
  simp only [Value.shell,Value.withFields,Value.head] at heads
  exact ⟨prior,reached,heads.symm.trans head⟩

theorem Value.AfterClearing.support {world : World} {original current : Value} {address observed : Address}
    {cleared : List Address} (pruned : original.AfterClearing address cleared current)
    (supported : current.Support world observed) : original.Support world observed := by
  obtain ⟨resident,authority,access,reached,edge⟩ := supported
  obtain ⟨prior,reached,shape,_⟩ := pruned.reachable reached
  refine ⟨prior,authority,access,reached,?_⟩
  rcases edge with ⟨identity,loan,head,found,referent⟩ | ⟨binding,member,referent⟩
  · have heads := congrArg Value.head shape
    simp only [Value.shell,Value.withFields,Value.head] at heads
    exact Or.inl ⟨identity,loan,heads.symm.trans head,found,referent⟩
  · have resources := congrArg Value.resources shape
    change resident.resources = prior.resources at resources
    exact Or.inr ⟨binding,resources ▸ member,referent⟩

theorem Value.SupportFramed.afterClearing {before after : World} {original current : Value} {address : Address}
    {cleared : List Address} (framed : original.SupportFramed before after)
    (pruned : original.AfterClearing address cleared current) : current.SupportFramed before after :=
  fun observed supported => framed observed (pruned.support supported)

theorem Value.BatchCompatible.afterClearing {before after : World} {original current : Value} {address : Address}
    {cleared : List Address} (batch : original.BatchCompatible before after)
    (pruned : original.AfterClearing address cleared current) : current.BatchCompatible before after := by
  refine ⟨fun identity authority access reached => batch.rows identity authority access (pruned.references reached),?_⟩
  intro resident authority access reached binding member held
  obtain ⟨prior,priorReach,shape,_⟩ := pruned.reachable reached
  have resources := congrArg Value.resources shape
  have owners := congrArg Value.owner shape
  change resident.resources = prior.resources at resources
  change resident.owner = prior.owner at owners
  have retained := batch.custody prior authority access priorReach binding (resources ▸ member)
    (by simpa only [owners] using held)
  simpa only [owners] using retained

/-- A declared invariant may inspect its resident's remaining fields. Closure
is therefore checked for the exact original-world residual, not inferred
from equality of shells or imposed as a new law on unsafe invariants. -/
theorem Value.ResourcesClosed.afterClearing {program : RuntimeProgram} {world : World} {original current : Value}
    {address : Address} {cleared : List Address} (closed : original.ResourcesClosed program world)
    (pruned : original.AfterClearing address cleared current)
    (residuals : ∀ path prior residual, ResidentAt original path prior →
      prior.AfterClearing { address with fields := address.fields ++ path } cleared residual → residual.InvariantClosed program world) :
    current.ResourcesClosed program world := by
  intro resident authority access reached
  obtain ⟨prior,priorReach,shape,origin⟩ := pruned.reachable reached
  obtain ⟨held,invariant⟩ := closed prior authority access priorReach
  have resources := congrArg Value.resources shape
  have owners := congrArg Value.owner shape
  change resident.resources = prior.resources at resources
  change resident.owner = prior.owner at owners
  refine ⟨fun binding member => ?_,?_⟩
  · simpa only [owners] using held binding (resources ▸ member)
  · rcases origin with rfl | ⟨path,located,residual⟩
    · exact invariant
    · exact residuals path prior resident located residual

theorem Value.LoansRestored.afterClearing {program : RuntimeProgram} {world : World} {original current : Value}
    {address : Address} {cleared : List Address} (restored : original.LoansRestored program world)
    (pruned : original.AfterClearing address cleared current) : current.LoansRestored program world :=
  fun identity authority access reached => restored identity authority access (pruned.references reached)


theorem Value.SupportFramed.trans_observed {before middle after : World} {value : Value}
    (rows : value.ReferenceRowsFramed before middle) (first : value.SupportFramed before middle)
    (last : value.SupportFramed middle after) : value.SupportFramed before after := by
  intro address supported
  have current := (Value.Support.frame_observed rows first).mp supported
  exact ⟨(last address current).1.trans (first address supported).1,
    (last address current).2.trans (first address supported).2⟩

theorem Value.BatchCompatible.trans {before middle after : World} {value : Value}
    (first : value.BatchCompatible before middle) (framed : value.SupportFramed before middle)
    (last : value.BatchCompatible middle after) : value.BatchCompatible before after := by
  constructor
  · intro identity authority access reached
    obtain ⟨resident,prior,head⟩ := reached
    have current : value.ReachableReference middle .owner .shared identity authority access :=
      ⟨resident,(Value.ReachableResident.frame_batch first framed).mp prior,head⟩
    exact (last.rows identity authority access current).trans (first.rows identity authority access ⟨resident,prior,head⟩)
  · intro resident authority access reached binding member held
    exact last.custody resident authority access ((Value.ReachableResident.frame_batch first framed).mp reached)
      binding member (first.custody resident authority access reached binding member held)


theorem Value.SupportOutside.frame_batch {before after : World} {value : Value} {written : Address}
    (outside : value.SupportOutside before written) (batch : value.BatchCompatible before after)
    (framed : value.SupportFramed before after) : value.SupportOutside after written :=
  fun observed supported => outside observed ((Value.Support.frame_batch batch framed).mpr supported)

end Glorious.Language
