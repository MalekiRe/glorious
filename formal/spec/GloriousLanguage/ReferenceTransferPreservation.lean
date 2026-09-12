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

theorem Authority.guardLoans_same_loans {before after : World} (loans : after.loans = before.loans)
    (authority : Authority) : authority.guardLoans after = authority.guardLoans before := by
  induction authority with
  | owner => rfl
  | loan identity => simp only [Authority.guardLoans,loans]
  | shared backing ih => exact ih
  | guarded backing carrier ih => simp only [Authority.guardLoans,loans,ih]

theorem Authority.referenceView_same_loans {before after : World} (loans : after.loans = before.loans)
    (authority : Authority) (identity : Identity) (access : Access) :
    authority.referenceView after identity access = authority.referenceView before identity access := by
  simp only [Authority.referenceView,Authority.throughReference,Authority.guardLoans_same_loans loans]

theorem Authority.resourceView_same_loans {before after : World} (loans : after.loans = before.loans)
    (authority : Authority) (binding : StorageBinding) (access : Access) :
    authority.resourceView after binding access = authority.resourceView before binding access := by
  simp only [Authority.resourceView,Authority.guardLoans_same_loans loans]

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

/-- Both directions use the same pre-state support. Backward traversal first
recovers the actual prior node before consulting its framed outgoing edge. -/
theorem Value.ReachableResident.frame {before after : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after) :
    value.ReachableResident before authority incoming resident current access ↔
      value.ReachableResident after authority incoming resident current access := by
  constructor
  · intro reached
    induction reached with
    | resident located => exact .resident located
    | @referent carrier parent parentAuthority parentAccess loan target path resident prior reference found stored located ih =>
        have preserved := (framed loan.referent (Value.Support.reference ⟨carrier,prior,reference⟩ found)).1
        have nextStored : after.Stores loan.referent target := preserved.trans stored
        simpa only [Authority.referenceView_same_loans loans] using
          Value.ReachableResident.referent ih reference (by simpa only [loans] using found) nextStored located
    | resource prior member stored located ih =>
        have preserved := (framed _ (Value.Support.resource prior member)).1
        simpa only [Authority.resourceView_same_loans loans] using
          Value.ReachableResident.resource ih member (preserved.trans stored) located
  · intro reached
    induction reached with
    | resident located => exact .resident located
    | @referent carrier parent parentAuthority parentAccess loan target path resident prior reference found stored located ih =>
        have oldFound : before.loans.get parent = some loan := by simpa only [loans] using found
        have preserved := (framed loan.referent (Value.Support.reference ⟨carrier,ih,reference⟩ oldFound)).1
        have oldStored : before.Stores loan.referent target := preserved.symm.trans stored
        simpa only [Authority.referenceView_same_loans loans] using
          Value.ReachableResident.referent ih reference oldFound oldStored located
    | resource _ member stored located ih =>
        have preserved := (framed _ (Value.Support.resource ih member)).1
        simpa only [Authority.resourceView_same_loans loans] using
          Value.ReachableResident.resource ih member (preserved.symm.trans stored) located

theorem Value.ReachableReference.frame {before after : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity}
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after) :
    value.ReachableReference before authority incoming identity current access ↔
      value.ReachableReference after authority incoming identity current access := by
  constructor
  · rintro ⟨resident,reached,reference⟩
    exact ⟨resident,(Value.ReachableResident.frame loans framed).mp reached,reference⟩
  · rintro ⟨resident,reached,reference⟩
    exact ⟨resident,(Value.ReachableResident.frame loans framed).mpr reached,reference⟩

theorem Value.Support.frame {before after : World} {value : Value} {address : Address}
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after) :
    value.Support before address ↔ value.Support after address := by
  constructor
  · rintro ⟨resident,authority,access,reached,edge⟩
    exact ⟨resident,authority,access,(Value.ReachableResident.frame loans framed).mp reached,
      by simpa only [loans] using edge⟩
  · rintro ⟨resident,authority,access,reached,edge⟩
    exact ⟨resident,authority,access,(Value.ReachableResident.frame loans framed).mpr reached,
      by simpa only [loans] using edge⟩

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

theorem Value.ResourcesClosed.frame {program : RuntimeProgram} {before after : World} {value : Value}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (closed : value.ResourcesClosed program before) : value.ResourcesClosed program after := by
  intro resident authority access reached
  have prior := (Value.ReachableResident.frame loans framed).mpr reached
  obtain ⟨held,declared⟩ := closed resident authority access prior
  refine ⟨fun binding member => (held binding member).frame locations loans,?_⟩
  unfold Value.InvariantClosed at declared ⊢
  cases type : resident.type with
  | nominal identity arguments =>
      simp only [type] at declared ⊢
      obtain ⟨data,found,contract⟩ := declared
      refine ⟨data,found,?_⟩
      cases invariant : data.invariant with
      | none => simpa only [invariant] using contract
      | some invariant =>
          simp only [invariant] at contract ⊢
          obtain ⟨selected,found,owner,holds⟩ := contract
          exact ⟨selected,found,owner,selected.framed before after resident (framed.reachable prior) holds⟩
  | _ => simpa only [type] using declared

theorem Value.LoansRestored.frame {program : RuntimeProgram} {before after : World} {value : Value}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (restored : value.LoansRestored program before) : value.LoansRestored program after := by
  intro identity authority access reached
  have prior := (Value.ReachableReference.frame loans framed).mpr reached
  obtain ⟨loan,found,live,⟨target,stored,initialized⟩,closed⟩ := restored identity authority access prior
  have preserved := (framed _ (Value.Support.reference prior found)).1
  refine ⟨loan,by simpa only [loans] using found,live,⟨target,preserved.trans stored,initialized⟩,?_⟩
  intro referent newStored
  have oldStored : before.Stores loan.referent referent := preserved.symm.trans newStored
  have nested := Value.ReachableResident.referent_prefix prior found oldStored (.resident (.root (value := referent)))
  exact (closed referent oldStored).frame locations loans (framed.reachable nested)

theorem Value.ReferencesAccessible.frame {before after : World} {value : Value}
    {authority : Authority} {incoming : Access}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (ready : value.ReferencesAccessible before authority incoming) : value.ReferencesAccessible after authority incoming := by
  intro identity current access reached
  obtain ⟨loan,found,live,permitted⟩ := ready identity current access
    ((Value.ReachableReference.frame loans framed).mpr reached)
  exact ⟨loan,by simpa only [loans] using found,live,
    by simpa only [Authority.referenceView_same_loans loans] using permitted.locationExtension locations loans⟩

theorem Value.ResourcesAccessible.frame {program : RuntimeProgram} {before after : World} {value : Value} {access : Access}
    (locations : before.LocationExtension after)
    (loans : after.loans = before.loans) (framed : value.SupportFramed before after)
    (ready : value.ResourcesAccessible program before access) : value.ResourcesAccessible program after access := by
  refine ⟨ready.1.frame locations loans framed,ready.2.1.frame locations loans framed,
    ready.references.frame locations loans framed,?_⟩
  intro resident authority incoming reached binding member
  have permitted := ready.2.2.2 resident authority incoming
    ((Value.ReachableResident.frame loans framed).mpr reached) binding member
  simpa only [Authority.resourceView_same_loans loans] using permitted.locationExtension locations loans

theorem Value.HandoffReady.frame {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access} {footprint : List Address}
    (locations : before.LocationExtension after) (loans : after.loans = before.loans)
    (framed : value.SupportFramed before after)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint := by
  refine ⟨ready.1.frame locations loans framed,?_⟩
  intro source member observed supported
  exact ready.2 source member observed ((Value.Support.frame loans framed).mpr supported)

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
