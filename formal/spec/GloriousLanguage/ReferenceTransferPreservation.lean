import GloriousLanguage.HandoffAccess

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

/-- Only the inherited guard list is observed while forming authority views.
An unrelated new loan with no guards preserves this observation even though
the complete loan tables differ. -/
def World.GuardsFramed (before after : World) : Prop :=
  ∀ identity, ((after.loans.get identity).map Loan.guards).getD [] =
    ((before.loans.get identity).map Loan.guards).getD []

theorem Authority.guardLoans_framed {before after : World} (guards : before.GuardsFramed after)
    (authority : Authority) : authority.guardLoans after = authority.guardLoans before := by
  induction authority with
  | owner => rfl
  | loan identity => exact guards identity
  | shared backing ih => exact ih
  | guarded backing carrier ih => simp only [Authority.guardLoans,guards carrier,ih]

theorem Authority.referenceView_framed {before after : World} (guards : before.GuardsFramed after)
    (authority : Authority) (identity : Identity) (access : Access) :
    authority.referenceView after identity access = authority.referenceView before identity access := by
  simp only [Authority.referenceView,Authority.throughReference,Authority.guardLoans_framed guards]

theorem Authority.resourceView_framed {before after : World} (guards : before.GuardsFramed after)
    (authority : Authority) (binding : StorageBinding) (access : Access) :
    authority.resourceView after binding access = authority.resourceView before binding access := by
  simp only [Authority.resourceView,Authority.guardLoans_framed guards]

theorem Authority.referenceView_of_guardLoans {before after : World} {authority : Authority}
    (guards : authority.guardLoans after = authority.guardLoans before) (identity : Identity) (access : Access) :
    authority.referenceView after identity access = authority.referenceView before identity access := by
  simp only [Authority.referenceView,Authority.throughReference,guards]

theorem Authority.resourceView_of_guardLoans {before after : World} {authority : Authority}
    (guards : authority.guardLoans after = authority.guardLoans before) (binding : StorageBinding) (access : Access) :
    authority.resourceView after binding access = authority.resourceView before binding access := by
  simp only [Authority.resourceView,guards]

theorem Authority.guardLoans_same_loans {before after : World} (loans : after.loans = before.loans)
    (authority : Authority) : authority.guardLoans after = authority.guardLoans before :=
  authority.guardLoans_framed (by intro identity; simp only [loans])

theorem Authority.referenceView_same_loans {before after : World} (loans : after.loans = before.loans)
    (authority : Authority) (identity : Identity) (access : Access) :
    authority.referenceView after identity access = authority.referenceView before identity access :=
  authority.referenceView_framed (by intro identity; simp only [loans]) identity access

theorem Authority.resourceView_same_loans {before after : World} (loans : after.loans = before.loans)
    (authority : Authority) (binding : StorageBinding) (access : Access) :
    authority.resourceView after binding access = authority.resourceView before binding access :=
  authority.resourceView_framed (by intro identity; simp only [loans]) binding access

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

/-- Fresh loans may add inherited guards at previously absent identities.
Existing recorded authorities observe only the retained rows. -/
def World.RecordedGuardsFramed (before after : World) : Prop :=
  ∀ identity loan, before.loans.get identity = some loan →
    (after.loans.get identity).map Loan.guards = some loan.guards

theorem Authority.Recorded.guards_framed {before after : World} {authority : Authority}
    (guards : before.RecordedGuardsFramed after) (recorded : authority.Recorded before.loans) :
    authority.guardLoans after = authority.guardLoans before := by
  induction authority with
  | owner => rfl
  | loan identity =>
      obtain ⟨loan,found⟩ := recorded
      simp only [Authority.guardLoans,found,guards identity loan found,Option.map_some,Option.getD_some]
  | shared backing ih => exact ih recorded
  | guarded backing carrier ih =>
      obtain ⟨loan,found⟩ := recorded.2
      simp only [Authority.guardLoans,found,guards carrier loan found,Option.map_some,Option.getD_some,ih recorded.1]

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
    (valid : world.WellFormed) (recorded : authority.Recorded world.loans)
    (found : world.loans.get identity = some loan) (access : Access) :
    (authority.referenceView world identity access).Recorded world.loans := by
  apply Authority.Recorded.lend
  apply Authority.Recorded.guarded_fold (authority := .loan identity) (loans := world.loans) ⟨loan,found⟩
  intro guard member
  rcases List.mem_append.mp member with parent | inherited
  · have parentAt : authority.parentLoan = some guard := Option.mem_toList.mp parent
    exact recorded.parentLoan parentAt
  · exact recorded.guardLoans valid guard inherited

theorem Authority.Recorded.resourceView {world : World} {authority : Authority} {binding : StorageBinding}
    (valid : world.WellFormed) (recorded : authority.Recorded world.loans)
    (resource : binding.authority.Recorded world.loans) (access : Access) :
    (authority.resourceView world binding access).Recorded world.loans := by
  apply Authority.Recorded.lend
  apply Authority.Recorded.guarded_fold resource
  intro guard member
  rcases List.mem_append.mp member with parent | inherited
  · exact recorded.parentLoan (Option.mem_toList.mp parent)
  · exact recorded.guardLoans valid guard inherited

theorem Authority.Recorded.resourceView_backing {world : World} {authority : Authority} {binding : StorageBinding} {access : Access}
    (recorded : (authority.resourceView world binding access).Recorded world.loans) :
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
    (valid : world.WellFormed) (resources : value.ResourcesRecorded world)
    (base : authority.Recorded world.loans)
    (reached : value.ReachableResident world authority incoming resident current access) :
    current.Recorded world.loans := by
  induction reached with
  | resident => exact base
  | referent _ _ found _ _ ih => exact ih.referenceView valid found _
  | resource prior member _ _ ih =>
      obtain ⟨current,access,prior⟩ := prior.rebase .owner .shared
      exact ih.resourceView valid (resources _ current access prior _ member) _

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
projection of every observed reference row is retained; every retained row
keeps the guards its recorded authorities observe; every observed retained
binding keeps its custody and its allocation-claim status. Custody and the
latest-owning-node law are separate fields because `Loan.permissionState`
erases both. -/
structure Value.BatchCompatible (before after : World) (value : Value) : Prop where
  rows : value.ReferenceRowsFramed before after
  guards : before.RecordedGuardsFramed after
  custody : value.HeldResourcesFramed before after

theorem Value.BatchCompatible.reachable {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (batch : value.BatchCompatible before after)
    (reached : value.ReachableResident before authority incoming resident current access) :
    resident.BatchCompatible before after :=
  ⟨batch.rows.reachable reached,batch.guards,batch.custody.reachable reached⟩

/-- Both directions use the same pre-state support and observed rows.
Backward traversal recovers the prior node before consulting its outgoing
edge. The unchanged-loan-table case below is only a wrapper around this walk. -/
theorem Value.ReachableResident.frame_scoped {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (rows : value.ReferenceRowsFramed before after)
    (guards : ∀ resident current access, value.ReachableResident before authority incoming resident current access →
      current.guardLoans after = current.guardLoans before)
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
        have view := Authority.referenceView_of_guardLoans (guards _ _ _ prior)
        simpa only [mode,view] using
          Value.ReachableResident.referent ih reference nextFound (referent ▸ nextStored) located
    | resource prior member stored located ih =>
        have preserved := (framed _ (Value.Support.resource prior member)).1
        simpa only [Authority.resourceView_of_guardLoans (guards _ _ _ prior)] using
          Value.ReachableResident.resource ih member (preserved.trans stored) located
  · intro reached
    induction reached with
    | resident located => exact .resident located
    | @referent carrier parent parentAuthority parentAccess loan target path resident prior reference found stored located ih =>
        obtain ⟨original,oldFound,shape⟩ := rows.selected_before ⟨carrier,ih,reference⟩ found
        have referent := (Loan.permissionState_eq_iff.mp shape).2.2.1
        have mode := (Loan.permissionState_eq_iff.mp shape).2.2.2.1
        have preserved := (framed original.referent (Value.Support.reference ⟨carrier,ih,reference⟩ oldFound)).1
        have oldStored : before.Stores original.referent target := preserved.symm.trans (referent ▸ stored)
        simpa only [mode,Authority.referenceView_of_guardLoans (guards _ _ _ ih)] using
          Value.ReachableResident.referent ih reference oldFound oldStored located
    | resource _ member stored located ih =>
        have preserved := (framed _ (Value.Support.resource ih member)).1
        simpa only [Authority.resourceView_of_guardLoans (guards _ _ _ ih)] using
          Value.ReachableResident.resource ih member (preserved.symm.trans stored) located

theorem Value.ReachableResident.frame_observed {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (rows : value.ReferenceRowsFramed before after) (guards : before.GuardsFramed after)
    (framed : value.SupportFramed before after) :
    value.ReachableResident before authority incoming resident current access ↔
      value.ReachableResident after authority incoming resident current access :=
  Value.ReachableResident.frame_scoped rows (fun _ current _ _ => current.guardLoans_framed guards) framed

theorem Value.ReachableResident.frame_batch {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (valid : before.WellFormed) (resources : value.ResourcesRecorded before)
    (base : authority.Recorded before.loans)
    (batch : value.BatchCompatible before after)
    (framed : value.SupportFramed before after) :
    value.ReachableResident before authority incoming resident current access ↔
      value.ReachableResident after authority incoming resident current access :=
  Value.ReachableResident.frame_scoped batch.rows
    (fun _ _ _ reached => (reached.recorded valid resources base).guards_framed batch.guards) framed

theorem Value.ReachableResident.frame {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after) :
    value.ReachableResident before authority incoming resident current access ↔
      value.ReachableResident after authority incoming resident current access :=
  Value.ReachableResident.frame_observed (by intro identity current access reached; rw [loans])
    (by intro identity; rw [loans]) framed

theorem Value.ReachableReference.frame_scoped {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity}
    (rows : value.ReferenceRowsFramed before after)
    (guards : ∀ resident current access, value.ReachableResident before authority incoming resident current access →
      current.guardLoans after = current.guardLoans before)
    (framed : value.SupportFramed before after) :
    value.ReachableReference before authority incoming identity current access ↔
      value.ReachableReference after authority incoming identity current access := by
  constructor
  · rintro ⟨resident,reached,reference⟩
    exact ⟨resident,(Value.ReachableResident.frame_scoped rows guards framed).mp reached,reference⟩
  · rintro ⟨resident,reached,reference⟩
    exact ⟨resident,(Value.ReachableResident.frame_scoped rows guards framed).mpr reached,reference⟩

theorem Value.ReachableReference.frame_observed {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity}
    (rows : value.ReferenceRowsFramed before after) (guards : before.GuardsFramed after)
    (framed : value.SupportFramed before after) :
    value.ReachableReference before authority incoming identity current access ↔
      value.ReachableReference after authority incoming identity current access :=
  Value.ReachableReference.frame_scoped rows (fun _ current _ _ => current.guardLoans_framed guards) framed

theorem Value.ReachableReference.frame_batch {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity}
    (valid : before.WellFormed) (resources : value.ResourcesRecorded before)
    (base : authority.Recorded before.loans)
    (batch : value.BatchCompatible before after)
    (framed : value.SupportFramed before after) :
    value.ReachableReference before authority incoming identity current access ↔
      value.ReachableReference after authority incoming identity current access :=
  Value.ReachableReference.frame_scoped batch.rows
    (fun _ _ _ reached => (reached.recorded valid resources base).guards_framed batch.guards) framed

theorem Value.ReachableReference.frame {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity}
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after) :
    value.ReachableReference before authority incoming identity current access ↔
      value.ReachableReference after authority incoming identity current access :=
  Value.ReachableReference.frame_observed (by intro identity current access reached; rw [loans])
    (by intro identity; rw [loans]) framed

theorem Value.Support.frame_scoped {before after : World} {value : Value} {address : Address}
    (rows : value.ReferenceRowsFramed before after)
    (guards : ∀ resident current access, value.ReachableResident before .owner .shared resident current access →
      current.guardLoans after = current.guardLoans before)
    (framed : value.SupportFramed before after) :
    value.Support before address ↔ value.Support after address := by
  constructor
  · rintro ⟨resident,authority,access,reached,edge⟩
    refine ⟨resident,authority,access,(Value.ReachableResident.frame_scoped rows guards framed).mp reached,?_⟩
    rcases edge with ⟨identity,loan,head,found,equal⟩ | resource
    · obtain ⟨changed,selected,shape⟩ := rows.selected ⟨resident,reached,head⟩ found
      exact Or.inl ⟨identity,changed,head,selected,(Loan.permissionState_eq_iff.mp shape).2.2.1.trans equal⟩
    · exact Or.inr resource
  · rintro ⟨resident,authority,access,reached,edge⟩
    have prior := (Value.ReachableResident.frame_scoped rows guards framed).mpr reached
    refine ⟨resident,authority,access,prior,?_⟩
    rcases edge with ⟨identity,loan,head,found,equal⟩ | resource
    · obtain ⟨original,selected,shape⟩ := rows.selected_before ⟨resident,prior,head⟩ found
      exact Or.inl ⟨identity,original,head,selected,(Loan.permissionState_eq_iff.mp shape).2.2.1.symm.trans equal⟩
    · exact Or.inr resource

theorem Value.Support.frame_observed {before after : World} {value : Value} {address : Address}
    (rows : value.ReferenceRowsFramed before after) (guards : before.GuardsFramed after)
    (framed : value.SupportFramed before after) :
    value.Support before address ↔ value.Support after address :=
  Value.Support.frame_scoped rows (fun _ current _ _ => current.guardLoans_framed guards) framed

theorem Value.Support.frame_batch {before after : World} {value : Value} {address : Address}
    (valid : before.WellFormed) (resources : value.ResourcesRecorded before)
    (batch : value.BatchCompatible before after)
    (framed : value.SupportFramed before after) :
    value.Support before address ↔ value.Support after address :=
  Value.Support.frame_scoped batch.rows
    (fun _ _ _ reached => (reached.recorded (authority := .owner) valid resources trivial).guards_framed batch.guards)
    framed

theorem Value.Support.frame {before after : World} {value : Value} {address : Address}
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after) :
    value.Support before address ↔ value.Support after address :=
  Value.Support.frame_observed (by intro identity current access reached; rw [loans])
    (by intro identity; rw [loans]) framed

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

theorem StorageBinding.HeldBy.frame {before after : World} {binding : StorageBinding} {owner : Identity}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (held : binding.HeldBy before owner) : binding.HeldBy after owner := by
  refine ⟨held.1.same_loans loans,?_⟩
  rcases held.2 with ⟨claim,writable⟩ | storage
  · exact Or.inl ⟨claim.frame locations loans,writable⟩
  · exact Or.inr (by simpa only [loans] using storage)

theorem Value.ResourcesClosed.frame_scoped {program : RuntimeProgram} {before after : World} {value : Value}
    (rows : value.ReferenceRowsFramed before after)
    (guards : ∀ resident current access, value.ReachableResident before .owner .shared resident current access →
      current.guardLoans after = current.guardLoans before)
    (framed : value.SupportFramed before after)
    (heldBy : value.HeldResourcesFramed before after)
    (closed : value.ResourcesClosed program before) : value.ResourcesClosed program after := by
  intro resident authority access reached
  have prior := (Value.ReachableResident.frame_scoped rows guards framed).mpr reached
  obtain ⟨held,declared⟩ := closed resident authority access prior
  exact ⟨fun binding member => heldBy resident authority access prior binding member (held binding member),
    declared.framed (framed.reachable prior)⟩

theorem Value.ResourcesClosed.frame_observed {program : RuntimeProgram} {before after : World} {value : Value}
    (rows : value.ReferenceRowsFramed before after) (guards : before.GuardsFramed after)
    (framed : value.SupportFramed before after)
    (heldBy : ∀ binding owner, StorageBinding.HeldBy before owner binding → binding.HeldBy after owner)
    (closed : value.ResourcesClosed program before) : value.ResourcesClosed program after :=
  closed.frame_scoped rows (fun _ current _ _ => current.guardLoans_framed guards) framed
    (fun resident _ _ _ binding _ held => heldBy binding resident.owner held)

theorem Value.ResourcesClosed.frame_batch {program : RuntimeProgram} {before after : World} {value : Value}
    (valid : before.WellFormed) (resources : value.ResourcesRecorded before)
    (batch : value.BatchCompatible before after)
    (framed : value.SupportFramed before after)
    (closed : value.ResourcesClosed program before) : value.ResourcesClosed program after :=
  closed.frame_scoped batch.rows
    (fun _ _ _ reached => (reached.recorded (authority := .owner) valid resources trivial).guards_framed batch.guards)
    framed batch.custody

theorem Value.ResourcesClosed.frame {program : RuntimeProgram} {before after : World} {value : Value}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (closed : value.ResourcesClosed program before) : value.ResourcesClosed program after :=
  closed.frame_observed (by intro identity current access reached; rw [loans])
    (by intro identity; rw [loans]) framed (fun _ _ held => held.frame locations loans)

theorem Value.LoansRestored.frame_observed {program : RuntimeProgram} {before after : World} {value : Value}
    (rows : value.ReferenceRowsFramed before after) (guards : before.GuardsFramed after)
    (framed : value.SupportFramed before after)
    (heldBy : ∀ binding owner, StorageBinding.HeldBy before owner binding → binding.HeldBy after owner)
    (restored : value.LoansRestored program before) : value.LoansRestored program after := by
  intro identity authority access reached
  have prior := (Value.ReachableReference.frame_observed rows guards framed).mpr reached
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
  exact (closed referent oldStored).frame_observed (rows.reachable nested) guards (framed.reachable nested) heldBy

theorem Value.LoansRestored.frame {program : RuntimeProgram} {before after : World} {value : Value}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (restored : value.LoansRestored program before) : value.LoansRestored program after :=
  restored.frame_observed (by intro identity current access reached; rw [loans])
    (by intro identity; rw [loans]) framed (fun _ _ held => held.frame locations loans)

theorem Value.ReferencesAccessible.frame_observed {before after : World} {value : Value}
    {authority : Authority} {incoming : Access}
    (rows : value.ReferenceRowsFramed before after) (guards : before.GuardsFramed after)
    (framed : value.SupportFramed before after)
    (permitted : ∀ authority access address, Permitted before authority access address → Permitted after authority access address)
    (ready : value.ReferencesAccessible before authority incoming) : value.ReferencesAccessible after authority incoming := by
  intro identity current access reached
  have prior := (Value.ReachableReference.frame_observed rows guards framed).mpr reached
  obtain ⟨loan,found,live,permission⟩ := ready identity current access prior
  obtain ⟨changed,selected,shape⟩ := rows.selected prior found
  obtain ⟨_,_,referent,mode,_,active,_,_⟩ := Loan.permissionState_eq_iff.mp shape
  exact ⟨changed,selected,active.trans live,
    by simpa only [referent,mode,Authority.referenceView_framed guards] using permitted _ _ _ permission⟩

theorem Value.ReferencesAccessible.frame {before after : World} {value : Value}
    {authority : Authority} {incoming : Access}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (ready : value.ReferencesAccessible before authority incoming) : value.ReferencesAccessible after authority incoming :=
  ready.frame_observed (by intro identity current access reached; rw [loans])
    (by intro identity; rw [loans]) framed (fun _ _ _ permission => permission.locationExtension locations loans)

theorem Value.ResourcesAccessible.frame_observed {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access}
    (rows : value.ReferenceRowsFramed before after) (guards : before.GuardsFramed after)
    (framed : value.SupportFramed before after)
    (heldBy : ∀ binding owner, StorageBinding.HeldBy before owner binding → binding.HeldBy after owner)
    (permitted : ∀ authority access address, Permitted before authority access address → Permitted after authority access address)
    (ready : value.ResourcesAccessible program before access) : value.ResourcesAccessible program after access := by
  refine ⟨ready.1.frame_observed rows guards framed heldBy,ready.2.1.frame_observed rows guards framed heldBy,
    ready.references.frame_observed rows guards framed permitted,?_⟩
  intro resident authority incoming reached binding member
  have permission := ready.2.2.2 resident authority incoming
    ((Value.ReachableResident.frame_observed rows guards framed).mpr reached) binding member
  simpa only [Authority.resourceView_framed guards] using permitted _ _ _ permission

theorem Value.ResourcesAccessible.frame {program : RuntimeProgram} {before after : World} {value : Value} {access : Access}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (ready : value.ResourcesAccessible program before access) : value.ResourcesAccessible program after access :=
  ready.frame_observed (by intro identity current access reached; rw [loans])
    (by intro identity; rw [loans]) framed (fun _ _ held => held.frame locations loans)
    (fun _ _ _ permission => permission.locationExtension locations loans)

theorem Value.HandoffReady.frame_observed {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access} {footprint : List Address}
    (rows : value.ReferenceRowsFramed before after) (guards : before.GuardsFramed after)
    (framed : value.SupportFramed before after)
    (heldBy : ∀ binding owner, StorageBinding.HeldBy before owner binding → binding.HeldBy after owner)
    (permitted : ∀ authority access address, Permitted before authority access address → Permitted after authority access address)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint := by
  refine ⟨ready.1.frame_observed rows guards framed heldBy permitted,?_⟩
  intro source member observed supported
  exact ready.2 source member observed ((Value.Support.frame_observed rows guards framed).mpr supported)

theorem Value.HandoffReady.frame {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access} {footprint : List Address}
    (locations : before.LocationExtension after) (loans : after.loans = before.loans)
    (framed : value.SupportFramed before after)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint :=
  ready.frame_observed (by intro identity current access reached; rw [loans])
    (by intro identity; rw [loans]) framed (fun _ _ held => held.frame locations loans)
    (fun _ _ _ permission => permission.locationExtension locations loans)

theorem Value.LoansRestored.frame_batch {program : RuntimeProgram} {before after : World} {value : Value}
    (valid : before.WellFormed) (resources : value.ResourcesRecorded before)
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (restored : value.LoansRestored program before) : value.LoansRestored program after := by
  intro identity authority access reached
  have prior := (Value.ReachableReference.frame_batch (authority := .owner) valid resources trivial batch framed).mpr reached
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
  exact (closed storedValue oldStored).frame_batch valid (resources.reachable nested) (batch.reachable nested)
    (framed.reachable nested)

/-- The observed graph carries a mutation to readiness. `permitted` ranges over
every recorded authority, which is exactly what a pure frame (unchanged loan
table) discharges. A step that inserts a row the source table never held cannot
satisfy it, because that row may overlap an address the graph already reads;
such a step must restrict the obligation to the views the graph actually
observes. -/
theorem Value.ReferencesAccessible.frame_batch {before after : World} {value : Value}
    {authority : Authority} {incoming : Access}
    (valid : before.WellFormed) (resources : value.ResourcesRecorded before)
    (base : authority.Recorded before.loans)
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : ∀ (authority : Authority) (access : Access) (address : Address),
      authority.Recorded before.loans →
      Permitted before authority access address → Permitted after authority access address)
    (ready : value.ReferencesAccessible before authority incoming) :
    value.ReferencesAccessible after authority incoming := by
  intro identity current access reached
  have prior := (Value.ReachableReference.frame_batch valid resources base batch framed).mpr reached
  obtain ⟨loan,found,live,permission⟩ := ready identity current access prior
  obtain ⟨changed,selected,shape⟩ := batch.rows.selected prior found
  obtain ⟨_,_,referent,mode,_,active,_,_⟩ := Loan.permissionState_eq_iff.mp shape
  obtain ⟨_,priorReach,_⟩ := prior
  have recorded := priorReach.recorded valid resources base
  have view := Authority.referenceView_of_guardLoans (authority := current)
    (recorded.guards_framed batch.guards) identity (ReferenceAccess access loan.mode)
  refine ⟨changed,selected,active.trans live,?_⟩
  have index := Authority.Recorded.referenceView valid recorded found (ReferenceAccess access loan.mode)
  have stated := permitted (current.referenceView before identity (ReferenceAccess access loan.mode))
    (ReferenceAccess access loan.mode) loan.referent index permission
  simpa only [referent,mode,view] using stated

theorem Value.ResourcesAccessible.frame_batch {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access}
    (valid : before.WellFormed)
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : ∀ (authority : Authority) (access : Access) (address : Address),
      authority.Recorded before.loans →
      Permitted before authority access address → Permitted after authority access address)
    (ready : value.ResourcesAccessible program before access) : value.ResourcesAccessible program after access := by
  have resources := ready.resourcesRecorded
  refine ⟨ready.1.frame_batch valid resources batch framed,ready.2.1.frame_batch valid resources batch framed,
    ready.references.frame_batch valid resources trivial batch framed permitted,?_⟩
  intro resident authority incoming reached binding member
  have prior :=
    (Value.ReachableResident.frame_batch (authority := .owner) valid resources trivial batch framed).mpr reached
  have recorded := prior.recorded (authority := .owner) valid resources trivial
  have permission := ready.2.2.2 resident authority incoming prior binding member
  obtain ⟨next,nextAccess,shared⟩ := prior.rebase .owner .shared
  have index := Authority.Recorded.resourceView valid recorded
    (resources resident next nextAccess shared binding member) incoming
  have stated := permitted (authority.resourceView before binding incoming) (ResourceAccess incoming binding)
    binding.address index permission
  simpa only [Authority.resourceView_of_guardLoans (authority := authority)
    (recorded.guards_framed batch.guards) binding incoming] using stated

theorem Value.HandoffReady.frame_batch {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access} {footprint : List Address}
    (valid : before.WellFormed)
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : ∀ (authority : Authority) (access : Access) (address : Address),
      authority.Recorded before.loans →
      Permitted before authority access address → Permitted after authority access address)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint :=
  ⟨ready.1.frame_batch valid batch framed permitted,
    fun source member observed supported =>
      ready.2 source member observed ((Value.Support.frame_batch valid (ready.1.resourcesRecorded) batch framed).mpr supported)⟩

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

/-- Retained rows keep the guards their recorded authorities observe, read from
the same permission projection. -/
theorem World.RecordedGuardsFramed.of_rows {before after : World}
    (rows : before.ResourceRowsRetained after) : before.RecordedGuardsFramed after := by
  intro identity loan found
  obtain ⟨current,currentFound,shape⟩ := rows.permissions identity loan found
  obtain ⟨_,_,_,_,_,_,_,guards⟩ := Loan.permissionState_eq_iff.mp shape
  rw [currentFound,Option.map_some,guards]

/-- The whole graph-level product of one real mutation, from its row package and
the row existence its observed readiness already carries. -/
theorem Value.BatchCompatible.of_rows {before after : World} {value : Value}
    (rows : before.ResourceRowsRetained after)
    (references : ∀ identity current access,
      value.ReachableReference before .owner .shared identity current access →
        ∃ loan, before.loans.get identity = some loan) :
    value.BatchCompatible before after :=
  ⟨Value.ReferenceRowsFramed.of_rows rows references,
   World.RecordedGuardsFramed.of_rows rows,
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

theorem World.RecordedGuardsFramed.of_custody_update {before after : World}
    {identity : Identity} {original : Loan} {newCustody : ClaimCustody} {requested : Bool}
    (found : before.loans.get identity = some original)
    (rows : after.loans = before.loans.set identity
      { original with custody := some newCustody, returnRequested := requested }) :
    before.RecordedGuardsFramed after := by
  intro observed loan' beforeFound
  by_cases same : observed = identity
  · subst same
    have sameRow : loan' = original := Option.some.inj (beforeFound.symm.trans found)
    rw [rows,Table.get_set,sameRow]
    rfl
  · rw [rows,Table.get_set_other _ _ _ _ same,beforeFound]
    rfl

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
   World.RecordedGuardsFramed.of_custody_update found rows,
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

end Glorious.Language
