import GloriousLanguage.InputBindingProgress
import GloriousLanguage.HandoffPreservation
import GloriousLanguage.ReferenceTransferPreservation
import GloriousLanguage.LoanCompatibility
import GloriousLanguage.LoanResourceRows
import GloriousLanguage.StorageWrites
import GloriousLanguage.BindingPersistence
import GloriousLanguage.ResidentMutationPreservation
import GloriousLanguage.InvocationInputs

/-! The one authoritative pre-state product for an ordered batch of ordinary
invocation inputs, and the ordered binder that consumes it.

Readiness at the source world is not enough: an earlier binding can revoke a
later pending permission (a fresh unique loan), invalidate a later observed
allocation claim (a fresh owning child), strip a later observed custody
witness, or write under a later resident's retained support. Each of those
channels is stated here as an actual observation of another input's pre-state
reachable reference/resource graph, never as a top-level authority/address
fact, and each is instantiated by the real rule the binder actually performs.

The same product protects the outputs the fold has already produced: every
batch value whose source graph was framed once stays framed by every later
binding, so an earlier output and a later pending input are preserved by the
identical obligations. -/
namespace Glorious.Language

/-! ## 1. The observed graph of one batch value -/

/-- The permission views a value's own pre-state reachable graph actually
reads: every source reference view, and every view of a reachable resource
binding. These are the views a fresh loan row can invalidate. -/
def Value.ObservedViews (world : World) (value : Value) (access : Access)
    (authority : Authority) (requested : Access) (address : Address) : Prop :=
  (∃ identity current viewAccess loan,
      value.ReachableReference world .owner access identity current viewAccess ∧
      world.loans.get identity = some loan ∧
      authority = current.referenceView identity (ReferenceAccess viewAccess loan.mode) ∧
      requested = ReferenceAccess viewAccess loan.mode ∧ address = loan.referent) ∨
  (∃ resident current incoming binding,
      value.ReachableResident world .owner access resident current incoming ∧
      binding ∈ resident.resources ∧
      authority = current.resourceView binding incoming ∧
      requested = ResourceAccess incoming binding ∧ address = binding.address)

/-- One fresh loan row, with its actual referent, mode and inherited guards, is
compatible with every permission the value's observed graph reads. This is the
exact pre-state criterion of `Permitted.fresh_loan`, indexed at the observers
the graph actually reads rather than at an arbitrary authority. -/
def Value.ViewsLoanCompatible (world : World) (value : Value) (access : Access)
    (referent : Address) (mode : Mutability) (guards : List Identity) : Prop :=
  ∀ authority requested address, value.ObservedViews world access authority requested address →
    authority.LoanCompatible world requested address referent mode guards

/-- The allocation claims the value's reachable resource bindings actually
read. Only these are constrained by a new owning child; ordinary storage and
reference descendants of an allocation coexist with a successor owner. -/
def Value.ObservedClaims (world : World) (value : Value)
    (authority : Authority) (address : Address) : Prop :=
  ∃ resident current incoming,
    value.ReachableResident world .owner .shared resident current incoming ∧
    ∃ binding ∈ resident.resources, authority = binding.authority ∧ address = binding.address

/-- A fresh row of the given kind and parent preserves the claim anchored at
the identity of every claim the value's reachable resources read. -/
def Value.ViewsClaimProtected (world : World) (value : Value)
    (kind : LoanKind) (parent : Option Identity) : Prop :=
  ∀ authority address, value.ObservedClaims world authority address →
    AllocationClaim world authority address →
      ∀ anchor, authority.parentLoan = some anchor → world.ClaimProtected kind parent anchor

/-- The authorities whose custody the value's reachable resource bindings
actually read. -/
def Value.ObservedCustody (world : World) (value : Value)
    (authority : Authority) : Prop :=
  ∃ resident current incoming,
    value.ReachableResident world .owner .shared resident current incoming ∧
    ∃ binding ∈ resident.resources, authority = binding.authority

/-- A custody move away from one recorded row leaves every authority the
value's reachable resources read outside that row's parent link. -/
def Value.ViewsCustodyKept (world : World) (value : Value) (identity : Identity) : Prop :=
  ∀ authority, value.ObservedCustody world authority → authority.parentLoan ≠ some identity

/-- A handoff-ready value reads all of its own observed permissions. This is
the consumer side of the graph restriction: the restricted frame hypothesis is
discharged from the actual source readiness, never assumed. -/
theorem Value.HandoffReady.observedPermitted {program : RuntimeProgram} {world : World}
    {value : Value} {access : Access} {footprint : List Address}
    (ready : value.HandoffReady program world access footprint) :
    ∀ authority requested address, value.ObservedViews world access authority requested address →
      Permitted world authority requested address := by
  intro authority requested address observed
  rcases observed with
    ⟨identity,current,viewAccess,loan,reached,found,atAuthority,atRequested,atAddress⟩ |
    ⟨resident,current,incoming,binding,reached,member,atAuthority,atRequested,atAddress⟩
  · obtain ⟨settled,selected,live,permission⟩ := ready.1.2.2.1 identity current viewAccess reached
    have same : loan = settled := Option.some.inj (found.symm.trans selected)
    subst atAuthority
    subst atRequested
    subst atAddress
    subst same
    exact permission
  · subst atAuthority
    subst atRequested
    subst atAddress
    exact ready.1.2.2.2 resident current incoming reached binding member

namespace Kernel

/-- The top-level permission read by the actual formal. Ordinary allocation
and raw-loan handoffs do not consume T through their token; only a guarded
allocation opening reads owned access. -/
def InvocationInput.ReadsAccess (input : InvocationInput) (requested : Access) : Prop :=
  match input.formal with
  | .resident _ | .storage _ _ => requested = input.access
  | .allocation _ _ => requested = .owned ∧ ∃ backing carrier, input.authority = .guarded backing carrier
  | .loan _ _ => False

/-- A permission the pending input's own readiness actually reads: its own
authority view, and, for a resident, the whole reachable graph of the value
stored at its storage. -/
def InvocationInput.ReadsPermission (world : World) (input : InvocationInput)
    (authority : Authority) (access : Access) (address : Address) : Prop :=
  (authority = input.authority ∧ address = input.storage ∧ input.ReadsAccess access ∧
    Permitted world input.authority access input.storage) ∨
  (∃ localSlot value, input.formal = .resident localSlot ∧ world.Stores input.storage value ∧
    value.ObservedViews world input.access authority access address)

/-- An allocation claim the pending input's readiness actually reads. -/
def InvocationInput.ReadsClaim (world : World) (input : InvocationInput)
    (authority : Authority) (address : Address) : Prop :=
  (authority = input.authority ∧ address = input.storage ∧ AllocationClaim world authority address) ∨
  (∃ localSlot value, input.formal = .resident localSlot ∧ world.Stores input.storage value ∧
    value.ObservedClaims world authority address)

/-- A custody view the pending input's readiness actually reads. -/
def InvocationInput.ReadsCustody (world : World) (input : InvocationInput)
    (authority : Authority) : Prop :=
  authority = input.authority ∨
  (∃ localSlot value, input.formal = .resident localSlot ∧ world.Stores input.storage value ∧
    value.ObservedCustody world authority)

/-- Support the pending input actually retains, through the value stored at its
storage. -/
def InvocationInput.RetainsSupport (world : World) (input : InvocationInput)
    (address : Address) : Prop :=
  ∃ localSlot value, input.formal = .resident localSlot ∧ world.Stores input.storage value ∧
    value.Support world address

/-- The one fresh loan row an actual binding step inserts, read from the
current pre-state. Owned residents, whole-allocation custody handoff and
storage-loan moves insert none. -/
def InvocationInput.FreshRow (world : World) (head : InvocationInput)
    (referent : Address) (mode : Mutability) (guards : List Identity) (kind : LoanKind) : Prop :=
  match head.formal with
  | .resident _ => head.access ≠ .owned ∧ referent = head.storage ∧ kind = .restoring ∧
      mode = (if head.access = .shared then .shared else .unique) ∧
      guards = head.authority.guardLoans world
  | .storage _ _ => referent = head.storage ∧ kind = .storageBorrow ∧
      mode = (if head.access = .shared then .shared else .unique) ∧
      guards = head.authority.guardLoans world
  | .allocation _ _ => (∃ backing carrier, head.authority = .guarded backing carrier) ∧
      referent = head.storage ∧ mode = .unique ∧ kind = .owning ∧
      guards = head.authority.guardLoans world
  | .loan _ _ => False

/-- The fresh owning row a binding inserts, with the parent node it inherits.
Only opening an allocation under a carrier borrow claims a new owning view. -/
def InvocationInput.FreshOwning (head : InvocationInput) (parent : Identity) : Prop :=
  (∃ identity type backing carrier,
      head.formal = .allocation identity type ∧ head.access = .owned ∧
      head.authority = .guarded backing carrier) ∧
  head.authority.parentLoan = some parent

/-- A custody write of one already-existing loan row: whole-allocation handoff
and the unique storage-loan move. Shared copies and fresh rows move nothing. -/
def InvocationInput.CustodyMoved (world : World) (head : InvocationInput) (identity : Identity) : Prop :=
  (∃ obligation type, head.formal = .allocation obligation type ∧ head.authority = .loan identity) ∨
  (∃ obligation type, head.formal = .loan obligation type ∧ head.authority = .loan identity ∧
    ∃ loan, world.loans.get identity = some loan ∧ loan.mode = .unique)

/-- The fresh root an actual resident allocation takes in this world. Every
real allocating rule uses `before.nextRoot`, so the retained-support exclusion
below is a genuine pre-state condition. -/
def FreshRoot (world : World) : Address := ⟨world.nextRoot,0,[]⟩

end Kernel

open Kernel

/-- Ordered pre-state independence of one actually executed head binding from
another input of the same batch: one conjunct per real invalidation channel,
each read from the other input's actual observed graph. -/
structure Kernel.InvocationInput.IndependentOf (program : RuntimeProgram) (footprint : List Address)
    (world : World) (head other : InvocationInput) : Prop where
  /-- (a) every fresh loan row the head inserts stays compatible with every
  permission the other input's observed graph reads. -/
  permission : ∀ referent mode guards kind, head.FreshRow world referent mode guards kind →
    ∀ authority access address, other.ReadsPermission world authority access address →
      authority.LoanCompatible world access address referent mode guards
  /-- (b) a fresh owning child must not supersede a claim the other input
  actually reads. -/
  claim : ∀ parent, head.FreshOwning parent →
    ∀ authority address, other.ReadsClaim world authority address →
      AllocationClaim world authority address →
        ∀ anchor, authority.parentLoan = some anchor →
          world.ClaimProtected .owning (some parent) anchor
  /-- (c) a custody write must not strip a loan the other input actually
  reads as custodian. -/
  custody : ∀ identity, head.CustodyMoved world identity →
    ∀ authority, other.ReadsCustody world authority → authority.parentLoan ≠ some identity
  /-- (d) the head's own clears must not touch the other input's storage. -/
  clear : ∀ address ∈ head.clearedStorage, ¬ address.Overlaps other.storage
  /-- (e) the head's fresh root must not land under the other input's retained
  support; the retained support exclusions are read from the actual graph. -/
  support : ∀ address, other.RetainsSupport world address → ¬ (FreshRoot world).Overlaps address

/-- The one authoritative PRE-STATE batch product: the source world makes the
whole ordered batch ready, and every ordered pair of distinct inputs satisfies
the graph-level independence above in that same world. The product constrains
both still-pending inputs and the outputs the fold has already produced, since
every binding of the batch is bound from one of these inputs' source values. -/
def Kernel.InvocationInputsCompatible (program : RuntimeProgram) (footprint : List Address)
    (region : Identity) (world : World) (inputs : List InvocationInput) : Prop :=
  InvocationInputsReadyFor program world footprint inputs ∧
  (∀ input ∈ inputs, InvocationInput.StorageRequest program world region input) ∧
  (∀ input ∈ inputs, input.authority.Recorded world.loans) ∧
  ∀ head ∈ inputs, ∀ other ∈ inputs, head ≠ other → head.IndependentOf program footprint world other

theorem Kernel.InvocationInputsCompatible.ready {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {world : World} {inputs : List InvocationInput}
    (compatible : InvocationInputsCompatible program footprint region world inputs) :
    InvocationInputsReadyFor program world footprint inputs :=
  compatible.1

theorem Kernel.InvocationInputsCompatible.requests {program : RuntimeProgram}
    {footprint : List Address} {region : Identity} {world : World} {inputs : List InvocationInput}
    (compatible : InvocationInputsCompatible program footprint region world inputs) :
    ∀ input ∈ inputs, InvocationInput.StorageRequest program world region input :=
  compatible.2.1

theorem Kernel.InvocationInputsCompatible.recorded {program : RuntimeProgram}
    {footprint : List Address} {region : Identity} {world : World} {inputs : List InvocationInput}
    (compatible : InvocationInputsCompatible program footprint region world inputs) :
    ∀ input ∈ inputs, input.authority.Recorded world.loans :=
  compatible.2.2.1

theorem Kernel.InvocationInputsCompatible.independent {program : RuntimeProgram}
    {footprint : List Address} {region : Identity} {world : World} {inputs : List InvocationInput}
    (compatible : InvocationInputsCompatible program footprint region world inputs)
    {head other : InvocationInput} (headMember : head ∈ inputs) (otherMember : other ∈ inputs)
    (different : head ≠ other) : head.IndependentOf program footprint world other :=
  compatible.2.2.2 head headMember other otherMember different

/-- The remaining batch inherits every pair obligation of the whole batch. -/
theorem Kernel.InvocationInputsCompatible.rest {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {world : World} {head : InvocationInput} {rest : List InvocationInput}
    (compatible : InvocationInputsCompatible program footprint region world (head :: rest)) :
    ∀ first ∈ rest, ∀ later ∈ rest, first ≠ later →
      first.IndependentOf program footprint world later :=
  fun _first firstMember _later laterMember different =>
    compatible.independent (List.mem_cons_of_mem head firstMember) (List.mem_cons_of_mem head laterMember) different

/-! ## 2. Row-level transport of the actual loan table

The binder changes the loan table in exactly two ways: one fresh row, or the
administrative fields of one existing row. Both directions of the resulting
row relation are read from the actual tables, and the fresh-row case is the
loan lane's own `Permitted.fresh_loan` criterion. -/

/-- The two-sided row relation of one administrative table update. -/
structure World.RowRelation (before after : World) : Prop where
  forward : ∀ identity loan, before.loans.get identity = some loan →
    ∃ current, after.loans.get identity = some current ∧ current.permissionState = loan.permissionState
  backward : ∀ identity loan, after.loans.get identity = some loan →
    ∃ source, before.loans.get identity = some source ∧ loan.permissionState = source.permissionState

theorem World.RowRelation.refl (world : World) : world.RowRelation world :=
  ⟨fun _ _ found => ⟨_,found,rfl⟩,fun _ _ found => ⟨_,found,rfl⟩⟩

theorem World.RowRelation.of_eq {before after : World} (loans : after.loans = before.loans) :
    before.RowRelation after := by
  constructor
  · intro key loan selected; exact ⟨loan,by rw [loans]; exact selected,rfl⟩
  · intro key loan selected; exact ⟨loan,by rw [← loans]; exact selected,rfl⟩

/-- One recorded row whose permission projection is unchanged. -/
theorem World.RowRelation.of_set {before after : World} {id : Identity} {original updated : Loan}
    (found : before.loans.get id = some original)
    (loans : after.loans = before.loans.set id updated)
    (shape : updated.permissionState = original.permissionState) : before.RowRelation after := by
  constructor
  · intro key loan selected
    by_cases same : key = id
    · subst same
      have equal : loan = original := Option.some.inj (selected.symm.trans found)
      exact ⟨updated,by rw [loans,Table.get_set],equal ▸ shape⟩
    · exact ⟨loan,by rw [loans,Table.get_set_other _ _ _ _ same]; exact selected,rfl⟩
  · intro key loan selected
    by_cases same : key = id
    · subst same
      refine ⟨original,found,?_⟩
      rw [loans,Table.get_set] at selected
      have equal : loan = updated := (Option.some.inj selected).symm
      rw [equal]; exact shape
    · refine ⟨loan,?_,rfl⟩
      rw [loans,Table.get_set_other _ _ _ _ same] at selected
      exact selected

theorem AncestorLoan.of_rows {before after : World}
    (rows : ∀ key loan, before.loans.get key = some loan → ∃ current,
      after.loans.get key = some current ∧ current.permissionState = loan.permissionState)
    {ancestor descendant : Identity} (related : AncestorLoan before ancestor descendant) :
    AncestorLoan after ancestor descendant := by
  induction related with
  | refl => exact .refl
  | parent selected link prior ih =>
      obtain ⟨current,present,shape⟩ := rows _ _ selected
      exact .parent present ((Loan.permissionState_eq_iff.mp shape).2.1.trans link) ih

theorem AncestorLoan.of_backward_rows {before after : World}
    (rows : ∀ key loan, after.loans.get key = some loan → ∃ source,
      before.loans.get key = some source ∧ loan.permissionState = source.permissionState)
    {ancestor descendant : Identity} (related : AncestorLoan after ancestor descendant) :
    AncestorLoan before ancestor descendant := by
  induction related with
  | refl => exact .refl
  | parent selected link prior ih =>
      obtain ⟨source,present,shape⟩ := rows _ _ selected
      exact .parent present ((Loan.permissionState_eq_iff.mp shape).2.1.symm.trans link) ih

/-- One administrative table update retains every source permission. The
exclusion clause is re-read through the retained rows in both directions. -/
theorem LoanPermission.of_rows {before after : World} (rows : before.RowRelation after)
    {id : Identity} {requested : Access} {address : Address}
    (permission : LoanPermission before id requested address) :
    LoanPermission after id requested address := by
  obtain ⟨active,found,live,root,generation,path,mode,exclusion,guards,dependent⟩ := permission
  obtain ⟨current,selected,shape⟩ := rows.forward _ _ found
  have fields := Loan.permissionState_eq_iff.mp shape
  refine ⟨current,selected,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [fields.2.2.2.2.2.1]; exact live
  · rw [fields.2.2.1]; exact root
  · rw [fields.2.2.1]; exact generation
  · rw [fields.2.2.1]; exact path
  · intro nonshared; rw [fields.2.2.2.1]; exact mode nonshared
  · intro other loan present alive different overlap conflict
    obtain ⟨original,source,sourceShape⟩ := rows.backward _ _ present
    have otherFields := Loan.permissionState_eq_iff.mp sourceShape
    have beforeLive : original.live = true := by rw [← otherFields.2.2.2.2.2.1]; exact alive
    have beforeOverlap : address.Overlaps original.referent := by rw [← otherFields.2.2.1]; exact overlap
    have beforeConflict : Conflict requested original.mode := by rw [← otherFields.2.2.2.1]; exact conflict
    exact (exclusion other original source beforeLive different beforeOverlap beforeConflict).of_rows rows.forward
  · intro guard member
    rw [fields.2.2.2.2.2.2.2] at member
    obtain ⟨loan,present,alive⟩ := guards guard member
    obtain ⟨current,selected,shape⟩ := rows.forward _ _ present
    exact ⟨current,selected,by rw [(Loan.permissionState_eq_iff.mp shape).2.2.2.2.2.1]; exact alive⟩
  · intro other loan present alive member
    obtain ⟨original,source,sourceShape⟩ := rows.backward _ _ present
    have otherFields := Loan.permissionState_eq_iff.mp sourceShape
    have beforeLive : original.live = true := by rw [← otherFields.2.2.2.2.2.1]; exact alive
    have beforeMember : id ∈ original.guards := by rw [← otherFields.2.2.2.2.2.2.2]; exact member
    exact dependent other original source beforeLive beforeMember

/-- Every permission of an observed authority survives one administrative
table update, provided the address still has a root. -/
theorem Permitted.of_rows {before after : World} (rows : before.RowRelation after)
    (roots : ∀ address root, before.root address = some root → ∃ changed, after.root address = some changed)
    {authority : Authority} {requested : Access} {address : Address}
    (permission : Permitted before authority requested address) :
    Permitted after authority requested address := by
  obtain ⟨root,selected⟩ := permission.root
  obtain ⟨changed,rootPresent⟩ := roots address root selected
  induction authority with
  | owner =>
      refine ⟨⟨changed,rootPresent⟩,?_⟩
      intro id loan found live overlap conflict
      obtain ⟨original,source,shape⟩ := rows.backward _ _ found
      have otherFields := Loan.permissionState_eq_iff.mp shape
      have beforeLive : original.live = true := by rw [← otherFields.2.2.2.2.2.1]; exact live
      exact permission.2 id original source beforeLive
        (by rw [← otherFields.2.2.1]; exact overlap)
        (by rw [← otherFields.2.2.2.1]; exact conflict)
  | loan id => exact ⟨⟨changed,rootPresent⟩,permission.2.of_rows rows⟩
  | shared backing ih => exact ⟨⟨changed,rootPresent⟩,permission.2.1,ih permission.2.2⟩
  | guarded backing carrier ih =>
      obtain ⟨loan,selected,guard⟩ := permission.2.2
      obtain ⟨current,present,shape⟩ := rows.forward _ _ selected
      rw [← (Loan.permissionState_eq_iff.mp shape).2.2.1] at guard
      exact ⟨⟨changed,rootPresent⟩,ih permission.2.1,current,present,guard.of_rows rows⟩

/-- One observed allocation claim survives one administrative table update. -/
theorem AllocationClaim.of_rows {before after : World}
    (rows : before.RowRelation after)
    (locations : before.LocationExtension after)
    {authority : Authority} {address : Address} (claim : AllocationClaim before authority address) :
    AllocationClaim after authority address := by
  obtain ⟨identity,loan,root,domain,parent,found,live,kind,referent,whole,selected,home,latest⟩ := claim
  obtain ⟨current,currentFound,shape⟩ := rows.forward _ _ found
  have fields := Loan.permissionState_eq_iff.mp shape
  obtain ⟨afterRoot,afterSelected,location⟩ := locations.root selected
  have homeEq : afterRoot.home = root.home := by
    simpa only [Root.location] using congrArg Root.home location
  refine ⟨identity,current,afterRoot,domain,parent,currentFound,?_,?_,?_,whole,afterSelected,?_,?_⟩
  · rw [fields.2.2.2.2.2.1]; exact live
  · rw [fields.2.2.2.2.2.2.1]; exact kind
  · rw [fields.2.2.1]; exact referent
  · rw [homeEq]; exact home
  · intro child successor present alive owning ancestry
    obtain ⟨original,source,sourceShape⟩ := rows.backward _ _ present
    have otherFields := Loan.permissionState_eq_iff.mp sourceShape
    have beforeAlive : original.live = true := by rw [← otherFields.2.2.2.2.2.1]; exact alive
    have beforeOwning : original.kind = .owning := by rw [← otherFields.2.2.2.2.2.2.1]; exact owning
    exact latest child original source beforeAlive beforeOwning (ancestry.of_backward_rows rows.backward)

/-- Custody of an observed authority whose own row is elsewhere survives one
administrative table update. This is the consumer side of the custody
obligation: the row that changes is never the observer's parent row. -/
theorem Authority.Custodied.of_row_update {before after : World} {identity : Identity}
    {replacement : Loan}
    (rows : after.loans = before.loans.set identity replacement)
    {authority : Authority} {custody : ClaimCustody}
    (kept : authority.parentLoan ≠ some identity)
    (held : authority.Custodied before custody) : authority.Custodied after custody :=
  Authority.Custodied.of_row_change rows (fun same => absurd same kept) held


/-! ## 3. Frame laws restricted to the observed graph

The universal `permitted` hypothesis of the general framers is not satisfiable
by a real fresh row: `.owner` is always recorded, and a source owner permission
disjoint from every existing loan still says nothing about the new row. The
hypothesis below is therefore indexed at exactly the views the value's own
source graph reads, which is what the batch product supplies. -/

/-- The observed permission views of one value, transported by one step. -/
def Value.FramePermitted (before after : World) (value : Value) (access : Access) : Prop :=
  ∀ authority requested address, value.ObservedViews before access authority requested address →
    Permitted before authority requested address → Permitted after authority requested address

theorem Value.ReferencesAccessible.frame_input {before after : World} {value : Value} {access : Access}
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : value.FramePermitted before after access)
    (ready : value.ReferencesAccessible before .owner access) :
    value.ReferencesAccessible after .owner access := by
  intro identity current access reached
  have prior := (Value.ReachableReference.frame_batch (authority := .owner) batch framed).mpr reached
  obtain ⟨loan,found,live,permission⟩ := ready identity current access prior
  obtain ⟨changed,selected,shape⟩ := batch.rows.selected prior found
  obtain ⟨_,_,referent,mode,_,active,_,_⟩ := Loan.permissionState_eq_iff.mp shape
  refine ⟨changed,selected,active.trans live,?_⟩
  have stated := permitted (current.referenceView identity (ReferenceAccess access loan.mode))
    (ReferenceAccess access loan.mode) loan.referent
    (Or.inl ⟨identity,current,access,loan,prior,found,rfl,rfl,rfl⟩) permission
  simpa only [referent,mode] using stated

theorem Value.ResourcesAccessible.frame_input {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access}
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : value.FramePermitted before after access)
    (ready : value.ResourcesAccessible program before access) :
    value.ResourcesAccessible program after access := by
  refine ⟨ready.1.frame_batch batch framed,ready.2.1.frame_batch batch framed,
    ready.references.frame_input batch framed permitted,?_⟩
  intro resident authority incoming reached binding member
  have prior := (Value.ReachableResident.frame_batch (authority := .owner) batch framed).mpr reached
  have permission := ready.2.2.2 resident authority incoming prior binding member
  exact permitted (authority.resourceView binding incoming)
    (ResourceAccess incoming binding) binding.address
    (Or.inr ⟨resident,authority,incoming,binding,prior,member,rfl,rfl,rfl⟩) permission

theorem Value.HandoffReady.frame_input {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access} {footprint : List Address}
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : value.FramePermitted before after access)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint :=
  ⟨ready.1.frame_input batch framed permitted,
    fun source member observed supported =>
      ready.2 source member observed
        ((Value.Support.frame_batch batch framed).mpr supported)⟩

/-! ## 4. Fresh-row and administrative-update row laws for the batch product -/

/-- A fresh row is inserted at the frontier, so every observed reference row
keeps its permission projection. -/
theorem Value.ReferenceRowsFramed.of_fresh_loan {program : RuntimeProgram} {before after : World}
    {fresh : Loan} {value : Value}
    (valid : before.WellFormed)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (restored : value.LoansRestored program before) :
    value.ReferenceRowsFramed before after := by
  intro identity current access reached
  obtain ⟨loan,found,live,_⟩ := restored identity current access reached
  rw [loans,Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid found)),found]

/-- The observed resource graph keeps every retained binding under one fresh
row, except for the claims the product states are superseded by an owning
child. -/
theorem Value.HeldResourcesFramed.of_fresh_loan {before after : World} {fresh : Loan} {value : Value}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (parentBound : ∀ p, fresh.parent = some p → p < before.nextLoan)
    (superseded : ∀ authority address, value.ObservedClaims before authority address →
      AllocationClaim before authority address →
        ∀ anchor, authority.parentLoan = some anchor →
          before.ClaimProtected fresh.kind fresh.parent anchor) :
    value.HeldResourcesFramed before after := by
  intro resident authority access reached binding member held
  obtain ⟨custodied,resource⟩ := held
  refine ⟨Authority.Custodied.fresh_loan valid loans custodied,?_⟩
  rcases resource with ⟨claim,readonly⟩ | ⟨claimId,claimLoan,parented,claimFound,live,kind,referent,readonly⟩
  · obtain ⟨anchor,anchorLoan,root,domain,atAnchor,rest⟩ := claim
    have recreated : AllocationClaim before binding.authority binding.address :=
      ⟨anchor,anchorLoan,root,domain,atAnchor,rest⟩
    have stated := superseded binding.authority binding.address
      ⟨resident,authority,access,reached,binding,member,rfl,rfl⟩ recreated anchor atAnchor
    exact Or.inl ⟨AllocationClaim.fresh_loan valid locations loans recreated atAnchor parentBound stated,
      readonly⟩
  · exact Or.inr ⟨claimId,claimLoan,parented,World.fresh_loan_retained valid loans claimFound,
      live,kind,referent,readonly⟩

/-- The whole compatibility product of one actual fresh row. -/
theorem Value.BatchCompatible.of_fresh_loan {program : RuntimeProgram} {before after : World}
    {fresh : Loan} {value : Value}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (restored : value.LoansRestored program before)
    (parentBound : ∀ p, fresh.parent = some p → p < before.nextLoan)
    (superseded : ∀ authority address, value.ObservedClaims before authority address →
      AllocationClaim before authority address →
        ∀ anchor, authority.parentLoan = some anchor →
          before.ClaimProtected fresh.kind fresh.parent anchor) :
    value.BatchCompatible before after :=
  ⟨Value.ReferenceRowsFramed.of_fresh_loan valid loans restored,
   Value.HeldResourcesFramed.of_fresh_loan valid locations loans parentBound superseded⟩

/-- Raw binding custody of an erased port whose own authority is not the row
being rewritten survives one administrative update. -/
theorem Authority.Custodied.of_row_update_kept {before after : World} {identity : Identity}
    {replacement : Loan}
    (rows : after.loans = before.loans.set identity replacement)
    {authority : Authority} {custody : ClaimCustody}
    (kept : authority.parentLoan ≠ some identity)
    (held : authority.Custodied before custody) : authority.Custodied after custody :=
  Authority.Custodied.of_row_change rows (fun same => absurd same kept) held


/-! ## 5. The actual binding step, observed by the rest of the batch -/

/-- A write-framing helper: a value's support survives one world write that
misses both the written address and the fresh root frontier. -/
theorem Value.SupportFramed.of_write {before after : World} {address : Address} {replacement : Option Value}
    {value : Value}
    (written : before.write address replacement = some after)
    (outside : ∀ observed, value.Support before observed → ¬ address.Overlaps observed)
    (root : ∀ observed, value.Support before observed → (after.roots.get observed.root).map Root.location =
      (before.roots.get observed.root).map Root.location) :
    value.SupportFramed before after :=
  fun observed supported =>
    ⟨World.write_disjoint written (outside observed supported),root observed supported⟩

/-- Two world writes, each outside the retained support, retain the graph. -/
theorem Value.SupportFramed.of_two_writes {before middle after : World} {first second : Address}
    {firstValue secondValue : Option Value} {value : Value}
    (cleared : before.write first firstValue = some middle)
    (installed : middle.write second secondValue = some after)
    (loans : middle.loans = before.loans)
    (firstOutside : ∀ observed, value.Support before observed → ¬ first.Overlaps observed)
    (secondOutside : ∀ observed, value.Support before observed → ¬ second.Overlaps observed) :
    value.SupportFramed before after := by
  have step : value.SupportFramed before middle :=
    Value.SupportFramed.of_write cleared firstOutside
      (fun observed _ => World.write_locations cleared observed.root)
  exact step.trans loans
    (Value.SupportFramed.of_write installed
      (fun observed supported => secondOutside observed ((Value.Support.frame loans step).mpr supported))
      (fun observed _ => World.write_locations installed observed.root))

/-- A step that changes no root and no read retains the graph of every value. -/
theorem Value.BatchCompatible.of_eq {before after : World} {value : Value}
    (locations : before.LocationExtension after) (loans : after.loans = before.loans) :
    value.BatchCompatible before after :=
  ⟨(fun _ _ _ _ => by rw [loans]),
   (fun resident authority access reached binding member held => held.frame locations loans)⟩

/-- The actual loan write constructs a ready reference from finite source
observations: it misses the source and its reachable support, and its new row
is compatible with the source graph's existing views. No resulting-world
readiness, permission or framing certificate is an input. -/
theorem FormsLoan.handed_off_ready {program : RuntimeProgram} {purpose : LoanPurpose}
    {before after : World} {authority : Authority} {mode : Mutability} {region : Identity}
    {referent destination : Address} {value : Value} (valid : before.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    (stored : before.Stores referent value) (separated : ¬ destination.Overlaps referent)
    (outside : value.SupportOutside before destination)
    (compatible : value.ViewsLoanCompatible before (if mode = .shared then .shared else .unique)
      referent mode (authority.guardLoans before)) :
    ∃ type, after.Stores destination (.resident before.nextOwner (.reference mode (.runtimeRegion region) type)
      (.reference before.nextLoan) true []) ∧
      (Value.resident before.nextOwner (.reference mode (.runtimeRegion region) type)
        (.reference before.nextLoan) true []).Initialized ∧
      (Value.resident before.nextOwner (.reference mode (.runtimeRegion region) type)
        (.reference before.nextLoan) true []).ResourcesAccessible program after .owned := by
  have source : value.Initialized ∧ value.ResourcesAccessible program before (if mode = .shared then .shared else .unique) := by
    cases borrowed with
    | borrow actual _ initialized _ _ ready _ _ _ _ _ =>
      have same := Option.some.inj (actual.symm.trans stored)
      exact same ▸ ⟨initialized,ready⟩
  have framed : value.SupportFramed before after := by
    cases borrowed with
    | borrow _ _ _ _ _ _ _ _ _ _ written =>
      have physical := Value.SupportFramed.of_write written outside (fun observed _ => World.write_locations written observed.root)
      exact physical
  have retained : after.Stores referent value := by
    cases borrowed with
    | borrow _ _ _ _ _ _ _ _ _ _ written => exact (World.write_disjoint written separated).trans stored
  have batch := Value.BatchCompatible.of_rows (borrowed.resourceRowsRetained valid)
    (value := value) (fun identity current access reached =>
      let ⟨loan,found,_⟩ := source.2.2.1 identity current access reached
      ⟨loan,found⟩)
  have ready := source.2.frame_input batch framed (fun query requested address views held =>
    borrowed.permitted valid held (compatible query requested address views))
  obtain ⟨type,handle,found⟩ := borrowed.created_handle
  refine ⟨type,handle,?_,?_⟩
  · intro path resident located
    cases located with
    | root => exact ⟨rfl,by simp [Value.fields]⟩
    | field field _ => simp [Value.fields] at field
  · apply Value.ResourcesAccessible.reference found retained source.1
    · simpa only [ReferenceAccess,reduceCtorEq,false_or] using ready
    · simpa only [ReferenceAccess,reduceCtorEq,false_or] using borrowed.borrower_permitted valid


namespace Kernel

/-- Everything an actual binding step is observed to do by one other input of
the same batch: which of that input's world facts survive, and how its own
retained value graph is framed. -/
structure StepObservation (program : RuntimeProgram) (footprint : List Address) (region : Identity)
    (before middle : World) (other : InvocationInput) : Prop where
  /-- Only resident formals observe stored values. Erased ports observe the
  location, claim and loan/custody fields below, even when contents change. -/
  stores : other.formal.IsResident → ∀ value, before.Stores other.storage value → middle.Stores other.storage value
  storesBack : other.formal.IsResident → ∀ value, middle.Stores other.storage value → before.Stores other.storage value
  /-- The step advances the storage frontier by at most one root, so a fresh
  root of the middle world still lies above every source support address. -/
  nextRootBound : before.nextRoot ≤ middle.nextRoot
  located : before.Located other.storage → middle.Located other.storage
  type : ∀ term, AddressType program.declarations before other.storage term →
    AddressType program.declarations middle other.storage term
  permitted : ∀ requested, other.ReadsAccess requested →
    Permitted before other.authority requested other.storage →
      Permitted middle other.authority requested other.storage
  claim : AllocationClaim before other.authority other.storage →
    AllocationClaim middle other.authority other.storage
  loans : ∀ identity loan, before.loans.get identity = some loan →
    ∃ current, middle.loans.get identity = some current ∧ current.permissionState = loan.permissionState
  loanRegion : ∀ identity loan, before.loans.get identity = some loan →
    ∃ current, middle.loans.get identity = some current ∧ current.region = loan.region
  borrowRegion : ∀ address regionId, other.authority.BorrowRegion before address regionId →
    other.authority.BorrowRegion middle address regionId
  regionState : before.RegionExtension middle
  /-- Only a resident input carries a value whose graph the batch observes;
  an erased port's storage is read as its own claim/loan record instead. -/
  value : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
    before.Stores other.storage value →
      value.BatchCompatible before middle ∧ value.SupportFramed before middle
  framePermitted : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
    before.Stores other.storage value →
      value.FramePermitted before middle other.access

end Kernel

namespace Kernel

/-- The uniform consequence of one step observation: the other input's whole
readiness is retained, including its pending physical request. -/
theorem InvocationInput.readyFor_of_observation {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before middle : World} {other : InvocationInput}
    (observation : StepObservation program footprint region before middle other)
    (ready : other.ReadyFor program before footprint) :
    other.ReadyFor program middle footprint := by
  cases other with
  | mk origin formal storage authority access =>
    cases formal with
    | resident localSlot =>
      obtain ⟨value,stored,initialized,type,handoff,permission⟩ := ready
      exact ⟨value,observation.stores trivial value stored,initialized,type,
        handoff.frame_input (observation.value localSlot value rfl stored).1
          (observation.value localSlot value rfl stored).2
          (observation.framePermitted localSlot value rfl stored),
        observation.permitted access rfl permission⟩
    | storage identity type =>
      obtain ⟨locatedType,located,permission⟩ := ready
      exact ⟨observation.type type locatedType,observation.located located,observation.permitted access rfl permission⟩
    | allocation identity type =>
      obtain ⟨owned,locatedType,claim,authorityForm⟩ := ready
      refine ⟨owned,observation.type type locatedType,observation.claim claim,?_⟩
      rcases authorityForm with ⟨loan,loanAt⟩ | ⟨backing,guard,guarded,permission⟩
      · exact Or.inl ⟨loan,loanAt⟩
      · exact Or.inr ⟨backing,guard,guarded,
          observation.permitted .owned ⟨rfl,backing,guard,guarded⟩ permission⟩
    | loan identity type =>
      obtain ⟨owned,locatedType,key,row,found,live,kind,referent,authorityForm⟩ := ready
      obtain ⟨changed,selected,shape⟩ := observation.loans key row found
      obtain ⟨_,_,referentEq,modeEq,_,liveEq,kindEq,_⟩ := Loan.permissionState_eq_iff.mp shape
      refine ⟨owned,observation.type type locatedType,key,changed,selected,?_,?_,?_,?_⟩
      · rw [liveEq]; exact live
      · rw [kindEq]; exact kind
      · rw [referentEq]; exact referent
      · rcases authorityForm with ⟨loanAt,unique⟩ | ⟨backing,shared,parent,mode⟩
        · exact Or.inl ⟨loanAt,by rw [modeEq]; exact unique⟩
        · exact Or.inr ⟨backing,shared,parent,by rw [modeEq]; exact mode⟩

/-- Every pending physical request of the other input is retained. -/
theorem InvocationInput.storageRequest_of_observation {program : RuntimeProgram}
    {footprint : List Address} {region : Identity} {before middle : World}
    {other : InvocationInput}
    (observation : StepObservation program footprint region before middle other)
    (request : other.StorageRequest program before region) :
    other.StorageRequest program middle region := by
  cases other with
  | mk origin formal storage authority access =>
    cases formal with
    | resident localSlot =>
      by_cases owned : access = .owned
      · subst owned
        obtain ⟨layout,request⟩ := request
        exact ⟨layout,request.retarget (observation.regionState.regions _ request.region_live)
          observation.regionState.frontier⟩
      · simp only [InvocationInput.StorageRequest,if_neg owned]
        simp only [InvocationInput.StorageRequest,if_neg owned] at request
        obtain ⟨loanRegion,layout,borrowed,sourceType,request⟩ := request
        exact ⟨loanRegion,layout,observation.borrowRegion storage loanRegion borrowed,
          observation.type localSlot.type sourceType,
          request.retarget (observation.regionState.regions _ request.region_live) observation.regionState.frontier⟩
    | storage _ _ | allocation _ _ | loan _ _ => exact trivial

end Kernel


/-- Every actual rule that writes or allocates keeps the region frontier: a
resident allocation consumes a fresh root, and a write consumes no region. -/
theorem World.write_region_state {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  obtain ⟨root,replacement,found,rfl⟩ := World.write_value_update written
  exact ⟨rfl,rfl⟩

theorem Allocates.region_state {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases allocated; exact ⟨rfl,rfl⟩

theorem Transfers.region_state {program : RuntimeProgram} {before after : World}
    {authority source destination}
    (moved : Transfers program before authority source destination after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases moved with
  | move _ _ _ _ _ _ _ clear install =>
      exact ⟨(World.write_region_state install).1.trans (World.write_region_state clear).1,
        (World.write_region_state install).2.trans (World.write_region_state clear).2⟩

theorem FormsLoan.region_state {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases borrowed with
  | borrow _ _ _ _ _ _ _ _ _ _ written =>
      have state := World.write_region_state written
      exact state

theorem ClaimsStorage.region_state {custody : ClaimCustody} {before after : World}
    {authority access address created}
    (claimed : ClaimsStorage custody before authority access address created after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases claimed; exact ⟨rfl,rfl⟩

theorem TransfersAllocation.region_state {recipient : ClaimCustody} {before after : World} {place}
    (transferred : TransfersAllocation recipient before place after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases transferred; exact ⟨rfl,rfl⟩

theorem TransfersStorageLoan.region_state {recipient : ClaimCustody} {before after : World} {place}
    (transferred : TransfersStorageLoan recipient before place after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases transferred <;> exact ⟨rfl,rfl⟩

theorem ClaimsAllocation.region_state {recipient : ClaimCustody} {before after : World}
    {authority address created}
    (claimed : ClaimsAllocation recipient before authority address created after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases claimed; exact ⟨rfl,rfl⟩

namespace Kernel

theorem LendsResident.region_state {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases lent with
  | owned => exact ⟨rfl,rfl⟩
  | lent _ _ _ allocated formed =>
      have first := Allocates.region_state allocated
      have second := FormsLoan.region_state formed
      exact ⟨second.1.trans first.1,second.2.trans first.2⟩

end Kernel

/-- A span of the region frontier is fixed by every actual binding rule: the
resident allocation path takes a fresh root, not a fresh region. -/
theorem Kernel.BindsInputAt.region_state {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : InvocationInput} {binding : Binding}
    (bound : BindsInputAt program recipient activation scope region before input binding after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact Kernel.LendsResident.region_state lent
  | owned _ _ _ _ _ allocated transferred =>
      have first := Allocates.region_state allocated
      have second := Transfers.region_state transferred
      exact ⟨second.1.trans first.1,second.2.trans first.2⟩
  | storage _ _ _ claimed => exact ClaimsStorage.region_state claimed
  | allocation _ _ _ _ transferred => exact TransfersAllocation.region_state transferred
  | guardedAllocation _ _ _ _ _ claimed => exact ClaimsAllocation.region_state claimed
  | loan _ _ _ _ transferred => exact TransfersStorageLoan.region_state transferred

/-! ## 6. Storage projections of the actual step

Every rule below keeps the live root table: an administrative loan update
rewrites only `loans`/`nextLoan`, and a fresh resident allocation writes at a
fresh root that no other input's storage can name. The read graph, locatedness
and declared address typing of another input therefore survive the step. -/

theorem World.root_of_roots {before after : World} (roots : after.roots = before.roots)
    (address : Address) : after.root address = before.root address := by
  simp only [World.root, roots]

theorem World.read_of_roots {before after : World} (roots : after.roots = before.roots)
    (address : Address) : after.read address = before.read address := by
  simp only [World.read, World.root, roots]

theorem World.Stores.of_roots {before after : World} (roots : after.roots = before.roots)
    {address : Address} {value : Value} (stored : before.Stores address value) :
    after.Stores address value := by
  rw [World.Stores] at stored ⊢
  rw [World.read_of_roots roots]
  exact stored

theorem World.Located.of_roots {before after : World} (roots : after.roots = before.roots)
    {address : Address} (located : before.Located address) : after.Located address := by
  rcases located with ⟨value,stored⟩ | ⟨root,selected,vacant⟩
  · exact Or.inl ⟨value,World.Stores.of_roots roots stored⟩
  · exact Or.inr ⟨root,by rw [World.root_of_roots roots]; exact selected,vacant⟩

theorem World.LocationExtension.of_roots {before after : World} (roots : after.roots = before.roots) :
    before.LocationExtension after :=
  World.LocationExtension.of_locations (fun _ => by rw [roots])

/-- The region record of every retained row survives one table rewrite. -/
theorem World.row_region_of {before after : World} {table : Table Loan}
    (loans : after.loans = table)
    (forward : ∀ identity loan, before.loans.get identity = some loan →
      ∃ current, table.get identity = some current ∧ current.region = loan.region) :
    ∀ identity loan, before.loans.get identity = some loan →
      ∃ current, after.loans.get identity = some current ∧ current.region = loan.region :=
  fun identity loan found => by
    obtain ⟨current,selected,region⟩ := forward identity loan found
    exact ⟨current,by rw [loans]; exact selected,region⟩

/-- Recorded borrow regions of a query authority survive one table rewrite plus
the location frame of the roots it names. -/
theorem Authority.BorrowRegion.transport {before after : World} {authority : Authority}
    {address : Address} {region : Identity}
    (extended : before.LocationExtension after)
    (rows : ∀ identity loan, before.loans.get identity = some loan →
      ∃ current, after.loans.get identity = some current ∧ current.region = loan.region)
    (borrowed : authority.BorrowRegion before address region) : authority.BorrowRegion after address region := by
  induction authority with
  | owner =>
      obtain ⟨root,found,regionAt⟩ := borrowed
      obtain ⟨current,selected,same⟩ := Option.map_eq_some_iff.mp (extended address.root root found)
      have regionEq : current.region = root.region := by
        simpa only [Root.location] using congrArg Root.region same
      exact ⟨current,selected,regionEq.trans regionAt⟩
  | loan identity =>
      obtain ⟨loan,found,regionAt⟩ := borrowed
      obtain ⟨current,selected,regionEq⟩ := rows identity loan found
      exact ⟨current,selected,regionEq.trans regionAt⟩
  | shared backing ih => exact ih borrowed
  | guarded backing carrier ih => exact ih borrowed

/-- Reachability is a property of the reachable resident, not of the view
labels along the path. This is the label-agnostic form the observed support
relation reads. -/
def Value.ReachableNode (world : World) (value resident : Value) : Prop :=
  ∃ authority incoming current access, value.ReachableResident world authority incoming resident current access

theorem Value.ReachableNode.reads_loans {before after : World} {value : Value}
    (reads : ∀ address, after.read address = before.read address) (loans : after.loans = before.loans) :
    ∀ {resident authority incoming current access},
      value.ReachableResident before authority incoming resident current access →
      Value.ReachableNode after value resident := by
  intro resident authority incoming current access reached
  induction reached with
  | @resident path resident located =>
      exact ⟨Authority.owner,Access.shared,Authority.owner,Access.shared,.resident located⟩
  | @referent carrier parent parentAuthority parentAccess loan target path resident
      prior reference found stored located ih =>
      obtain ⟨a,i,c,ac,nested⟩ := ih
      exact ⟨a,i,c.referenceView parent (ReferenceAccess ac loan.mode),ReferenceAccess ac loan.mode,
        .referent nested reference (by rw [loans]; exact found)
          (by rw [World.Stores] at stored ⊢; rw [reads]; exact stored) located⟩
  | @resource carrier current access binding target path resident prior member stored located ih =>
      obtain ⟨a,i,c,ac,nested⟩ := ih
      exact ⟨a,i,c.resourceView binding ac,ResourceAccess ac binding,
        .resource nested member (by rw [World.Stores] at stored ⊢; rw [reads]; exact stored) located⟩

theorem Value.Support.reads_loans {before after : World} {value : Value} {address : Address}
    (reads : ∀ address, after.read address = before.read address) (loans : after.loans = before.loans) :
    value.Support before address ↔ value.Support after address := by
  constructor
  · rintro ⟨resident,authority,access,reached,edge⟩
    obtain ⟨a,i,c,ac,nested⟩ := Value.ReachableNode.reads_loans reads loans reached
    obtain ⟨next,nextAccess,nested⟩ := nested.rebase Authority.owner .shared
    refine ⟨resident,next,nextAccess,nested,?_⟩
    rcases edge with ⟨identity,loan,head,found,equal⟩ | resource
    · exact Or.inl ⟨identity,loan,head,by rw [loans]; exact found,equal⟩
    · exact Or.inr resource
  · rintro ⟨resident,authority,access,reached,edge⟩
    obtain ⟨a,i,c,ac,nested⟩ :=
      Value.ReachableNode.reads_loans (fun a => (reads a).symm) loans.symm reached
    obtain ⟨next,nextAccess,nested⟩ := nested.rebase Authority.owner .shared
    refine ⟨resident,next,nextAccess,nested,?_⟩
    rcases edge with ⟨identity,loan,head,found,equal⟩ | resource
    · exact Or.inl ⟨identity,loan,head,by rw [← loans]; exact found,equal⟩
    · exact Or.inr resource

theorem Value.SupportOutside.reads_loans {before after : World} {value : Value} {mutation : Address}
    (reads : ∀ address, after.read address = before.read address) (loans : after.loans = before.loans) :
    value.SupportOutside before mutation ↔ value.SupportOutside after mutation :=
  ⟨fun outside address supported => outside address ((Value.Support.reads_loans reads loans).mpr supported),
   fun outside address supported => outside address ((Value.Support.reads_loans reads loans).mp supported)⟩

theorem World.rooted_bound {world : World} {address : Address} {root : Root}
    (valid : world.WellFormed) (found : world.root address = some root) :
    address.root < world.nextRoot :=
  World.root_bound valid (World.root_found found).1

theorem Permitted.rooted_bound {world : World} {authority : Authority} {access : Access} {address : Address}
    (valid : world.WellFormed) (permission : Permitted world authority access address) :
    address.root < world.nextRoot := by
  obtain ⟨root,found⟩ := permission.root
  exact World.rooted_bound valid found

theorem World.Stores.rooted_bound {world : World} {address : Address} {value : Value}
    (valid : world.WellFormed) (stored : world.Stores address value) : address.root < world.nextRoot := by
  obtain ⟨root,found,_⟩ := Option.bind_eq_some_iff.mp stored
  exact World.rooted_bound valid found

/-- Every support address of a usable value is already rooted in the source
world: reference support is read through the value's own permitted views and
resource support through the retained bindings' permissions. -/
theorem Value.Support.root_bound {program : RuntimeProgram} {world : World} {value : Value} {access : Access}
    (valid : world.WellFormed) (ready : value.ResourcesAccessible program world access) :
    ∀ {address}, value.Support world address → address.root < world.nextRoot := by
  intro address supported
  obtain ⟨resident,authority,incoming,reached,edge⟩ := supported
  rcases edge with ⟨identity,loan,head,found,equal⟩ | ⟨binding,member,bindingEq⟩
  · obtain ⟨next,nextAccess,reference⟩ :=
      Value.ReachableReference.rebase (⟨resident,reached,head⟩ : Value.ReachableReference world value Authority.owner
        .shared identity authority incoming) Authority.owner access
    obtain ⟨loan',found',_,permitted'⟩ := ready.2.2.1 identity next nextAccess reference
    have same : loan = loan' := Option.some.inj (found.symm.trans found')
    have target : loan'.referent = address := by rw [← same]; exact equal
    rw [← target]
    exact Permitted.rooted_bound valid permitted'
  · obtain ⟨next,nextAccess,reached'⟩ := reached.rebase Authority.owner access
    have permitted := ready.2.2.2 resident next nextAccess reached' binding member
    rw [← bindingEq]
    exact Permitted.rooted_bound valid permitted

/-- A fresh root cannot be the storage of any ready other input. -/
theorem Kernel.InvocationInput.ReadyFor.root_bound {program : RuntimeProgram} {world : World}
    {footprint : List Address} {input : InvocationInput} (valid : world.WellFormed)
    (ready : input.ReadyFor program world footprint) : input.storage.root < world.nextRoot := by
  cases input with
  | mk origin formal storage authority access =>
    cases formal with
    | resident localSlot =>
      obtain ⟨value,stored,_⟩ := ready
      exact World.Stores.rooted_bound valid stored
    | storage identity type =>
      obtain ⟨located,_,_⟩ := ready
      obtain ⟨root,found⟩ := AddressType.root_exists located
      exact World.rooted_bound valid found
    | allocation identity type =>
      obtain ⟨_,located,_,_⟩ := ready
      obtain ⟨root,found⟩ := AddressType.root_exists located
      exact World.rooted_bound valid found
    | loan identity type =>
      obtain ⟨_,located,_,_,_,_,_,_,_⟩ := ready
      obtain ⟨root,found⟩ := AddressType.root_exists located
      exact World.rooted_bound valid found

/-! ## 7. The actual binding step observed by the rest of the batch

Each of the six real rules is dispatched once here. The four erased-port rules
rewrite only the administrative loan table, so the read graph, locatedness and
declared address typing of another input survive by the root table alone. The
two resident rules additionally consume a fresh root for their destination and,
for an owned formal, clear exactly the storage the batch footprint already
covers; both exclusions come from the product's actual observed channels. -/

theorem Allocates.fresh_address {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    address = Kernel.FreshRoot before := by
  cases allocated
  rfl

theorem World.not_overlaps_of_root_ne {left right : Address} (different : left.root ≠ right.root) :
    ¬ left.Overlaps right := fun overlap => different overlap.1

theorem World.Stores.of_read {before after : World} (reads : ∀ address, after.read address = before.read address)
    {address : Address} {value : Value} (stored : before.Stores address value) : after.Stores address value := by
  rw [World.Stores] at stored ⊢
  rw [reads]
  exact stored

theorem World.Stores.write_other {before after : World} {mutation address : Address} {value : Option Value}
    (written : before.write mutation value = some after) (apart : ¬ mutation.Overlaps address)
    {resident : Value} (stored : before.Stores address resident) : after.Stores address resident := by
  rw [World.Stores] at stored ⊢
  rw [World.write_disjoint written apart]
  exact stored

/-- A resident formal is exactly a local slot. -/
theorem Kernel.InputFormal.exists_resident_of_isResident {formal : InputFormal} (resident : formal.IsResident) :
    ∃ localSlot, formal = .resident localSlot := by
  cases formal with
  | resident localSlot => exact ⟨localSlot,rfl⟩
  | storage identity type => exact absurd resident (by simp [InputFormal.IsResident])
  | allocation identity type => exact absurd resident (by simp [InputFormal.IsResident])
  | loan identity type => exact absurd resident (by simp [InputFormal.IsResident])

/-- Compatibility is read from the actual loan table, so a table equality
transports it in both directions. -/
theorem Authority.LoanCompatible.loans_congr {before after : World} {authority : Authority}
    {requested : Access} {address referent : Address} {mode : Mutability} {guards : List Identity}
    (loans : after.loans = before.loans)
    (compatible : authority.LoanCompatible before requested address referent mode guards) :
    authority.LoanCompatible after requested address referent mode guards := by
  induction authority with
  | owner => exact compatible
  | loan identity => exact compatible
  | shared backing ih => exact ih compatible
  | guarded backing carrier ih =>
      refine ⟨ih compatible.1,?_⟩
      intro loan found
      exact compatible.2 loan (by rw [← loans]; exact found)

/-- The region record of every retained row of one fresh insertion. -/
theorem World.fresh_loan_region {before after : World} {fresh : Loan}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh) :
    ∀ identity loan, before.loans.get identity = some loan →
      ∃ current, after.loans.get identity = some current ∧ current.region = loan.region :=
  fun identity loan found =>
    ⟨loan,by rw [loans,Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid found))]; exact found,rfl⟩

/-- The retained-region record of a two-sided row relation. -/
theorem World.RowRelation.region_rows {before after : World} (rows : World.RowRelation before after) :
    ∀ identity loan, before.loans.get identity = some loan →
      ∃ current, after.loans.get identity = some current ∧ current.region = loan.region := by
  intro identity loan found
  obtain ⟨current,selected,shape⟩ := rows.forward identity loan found
  exact ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩

theorem Value.ReferenceRowsFramed.of_row_relation {before after : World} {value : Value}
    (rows : World.RowRelation before after)
    (references : ∀ identity current access,
      value.ReachableReference before .owner .shared identity current access →
        ∃ loan, before.loans.get identity = some loan) :
    value.ReferenceRowsFramed before after := by
  intro identity current access reached
  obtain ⟨loan,found⟩ := references identity current access reached
  obtain ⟨changed,selected,shape⟩ := rows.forward identity loan found
  rw [selected,found,Option.map_some,Option.map_some,shape]

namespace Kernel

/-- The whole step observation of a rule that only rewrites the loan table. -/
theorem StepObservation.of_loans {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before middle : World} {other : InvocationInput}
    (roots : middle.roots = before.roots)
    (nextRootBound : before.nextRoot ≤ middle.nextRoot)
    (regionState : before.RegionExtension middle)
    (permissionRows : ∀ identity loan, before.loans.get identity = some loan →
      ∃ current, middle.loans.get identity = some current ∧ current.permissionState = loan.permissionState)
    (regionRows : ∀ identity loan, before.loans.get identity = some loan →
      ∃ current, middle.loans.get identity = some current ∧ current.region = loan.region)
    (permitted : ∀ authority access address, other.ReadsPermission before authority access address →
      Permitted before authority access address → Permitted middle authority access address)
    (claim : ∀ authority address, other.ReadsClaim before authority address →
      AllocationClaim before authority address → AllocationClaim middle authority address)
    (compatible : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.BatchCompatible before middle)
    (framed : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.SupportFramed before middle)
    (framePermitted : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.FramePermitted before middle other.access) :
    StepObservation program footprint region before middle other where
  stores := fun _ _ stored => World.Stores.of_roots roots stored
  storesBack := fun _ _ stored => World.Stores.of_roots roots.symm stored
  nextRootBound := nextRootBound
  located := World.Located.of_roots roots
  type := fun _ located => AddressType.roots_congr roots located
  permitted := fun requested observed permission => permitted _ requested _ (Or.inl ⟨rfl,rfl,observed,permission⟩) permission
  claim := fun held => claim _ _ (Or.inl ⟨rfl,rfl,held⟩) held
  loans := permissionRows
  loanRegion := regionRows
  borrowRegion := fun _ _ borrowed =>
    Authority.BorrowRegion.transport (World.LocationExtension.of_roots roots) regionRows borrowed
  regionState := regionState
  value := fun localSlot value formal stored =>
    ⟨compatible localSlot value formal stored,framed localSlot value formal stored⟩
  framePermitted := framePermitted

end Kernel

/-- The row one whole-allocation handoff moves, with the moved identity. -/
theorem TransfersAllocation.row_relation {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersAllocation recipient before place after) :
    World.RowRelation before after := by
  cases moved with
  | transfer authorityEq claim found =>
    rename_i identity loan
    refine World.RowRelation.of_set found rfl ?_
    simp only [Loan.permissionState]

theorem TransfersAllocation.roots_eq {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersAllocation recipient before place after) :
    after.roots = before.roots := by cases moved; rfl

theorem TransfersAllocation.moved_authority {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersAllocation recipient before place after) :
    ∃ identity, place.authority = .loan identity := by
  cases moved with
  | transfer authorityEq claim found => exact ⟨_,authorityEq⟩

theorem TransfersStorageLoan.row_relation {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersStorageLoan recipient before place after) :
    World.RowRelation before after := by
  cases moved with
  | unique authorityEq found live kind mode referent =>
    rename_i identity loan
    refine World.RowRelation.of_set found rfl ?_
    simp only [Loan.permissionState]
  | shared backingProof parent found live kind mode referent => exact World.RowRelation.refl before

theorem TransfersStorageLoan.roots_eq {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersStorageLoan recipient before place after) :
    after.roots = before.roots := by cases moved <;> rfl

theorem TransfersStorageLoan.moved_authority {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersStorageLoan recipient before place after) :
    (∃ identity, place.authority = .loan identity) ∨ ∃ backing, place.authority = .shared backing := by
  cases moved with
  | unique authorityEq found live kind mode referent => exact Or.inl ⟨_,authorityEq⟩
  | shared backingProof parent found live kind mode referent =>
    rename_i backingB identityB loanB
    exact Or.inr ⟨backingB,backingProof⟩



/-! ## 8. The record layer one actual binding step retains

Every binding rule changes at most one loan row, at the loan frontier, and
installs at most one root, at the storage frontier. The three facts below are
the whole retained-record product the pending tail consumes: each recorded row
below the frontier keeps its permission projection, each recorded root below
the frontier keeps its location, and no allocation or external claim is
anchored at a root the step created. -/

open Kernel

/-- The root an actual allocation installs carries exactly the home the
allocating rule selected; no other record is written at that identity. -/
theorem Allocates.created_home {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    ∀ record, after.roots.get address.root = some record → record.home = home := by
  intro record found
  cases allocated with
  | fresh request extent =>
    rw [Table.get_set] at found
    rw [← Option.some.inj found]

structure Kernel.StepFrame (before middle : World) : Prop where
  retained : ∀ id, id ≠ before.nextLoan →
    (middle.loans.get id).map Loan.permissionState = (before.loans.get id).map Loan.permissionState
  /-- Every recorded root below the storage frontier keeps its location: the
  step installs at most one root, at the frontier itself. -/
  rooted : ∀ id, id < before.nextRoot →
    (middle.roots.get id).map Root.location = (before.roots.get id).map Root.location
  /-- Every recorded allocation/external root is below the original frontier. -/
  anchored : ∀ id root, middle.roots.get id = some root →
    ((∃ domain, root.home = .allocation domain) ∨ ∃ domain, root.home = .external domain) →
      id < before.nextRoot

theorem StepFrame.row_of_before {before middle : World} (valid : before.WellFormed)
    (frame : StepFrame before middle) {id : Identity} {loan : Loan}
    (found : before.loans.get id = some loan) :
    ∃ current, middle.loans.get id = some current ∧ current.permissionState = loan.permissionState := by
  have same := frame.retained id (Nat.ne_of_lt (World.loanBounds valid found))
  simp only [found,Option.map_some] at same
  obtain ⟨current,selected,shape⟩ := Option.map_eq_some_iff.mp same
  exact ⟨current,selected,shape⟩

theorem StepFrame.row_of_middle {before middle : World} (frame : StepFrame before middle)
    {id : Identity} {loan : Loan} (bound : id < before.nextLoan) (found : middle.loans.get id = some loan) :
    ∃ source, before.loans.get id = some source ∧ source.permissionState = loan.permissionState := by
  have same := (frame.retained id (Nat.ne_of_lt bound)).symm
  simp only [found,Option.map_some] at same
  obtain ⟨source,selected,shape⟩ := Option.map_eq_some_iff.mp same
  exact ⟨source,selected,shape⟩

/-- A root below the frontier is recorded at the source world too, with its
home unchanged. -/
theorem Kernel.StepFrame.root_of_middle {before middle : World} (frame : StepFrame before middle)
    {address : Address} {root : Root} (bound : address.root < before.nextRoot)
    (found : middle.root address = some root) :
    ∃ source, before.root address = some source ∧ root.home = source.home := by
  obtain ⟨selected,live,generation⟩ := World.root_found found
  have table := frame.rooted address.root bound
  rw [selected] at table
  simp only [Option.map_some] at table
  obtain ⟨source,sourceFound,location⟩ := Option.map_eq_some_iff.mp table.symm
  have liveEq : source.live = root.live := by
    simpa only [Root.location] using congrArg Root.live location
  have generationEq : source.generation = root.generation := by
    simpa only [Root.location] using congrArg Root.generation location
  have sourceLive : source.live = true := liveEq.trans live
  have sourceGeneration : source.generation = address.generation :=
    generationEq.trans generation
  refine ⟨source,?_,by simpa only [Root.location] using congrArg Root.home location.symm⟩
  show before.root address = some source
  simp [World.root,sourceFound,sourceLive,sourceGeneration]

/-- An allocation or external claim is never anchored at a root the step
created. -/
theorem Kernel.StepFrame.anchored_root {before middle : World} (frame : StepFrame before middle)
    {address : Address} {root : Root} (found : middle.root address = some root)
    (home : (∃ domain, root.home = .allocation domain) ∨ ∃ domain, root.home = .external domain) :
    address.root < before.nextRoot :=
  frame.anchored address.root root (World.root_found found).1 home

/-- Recorded authorities observe the same guards after the step: every identity
they name is recorded at the source world, hence below the loan frontier. -/
theorem Kernel.StepFrame.guards {before middle : World} (valid : before.WellFormed)
    (frame : StepFrame before middle) {authority : Authority}
    (recorded : authority.Recorded before.loans) :
    authority.guardLoans middle = authority.guardLoans before := by
  induction authority with
  | owner => rfl
  | loan identity =>
      obtain ⟨loan,found⟩ := recorded
      obtain ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
      simp only [Authority.guardLoans,found,selected,Option.map_some,Option.getD_some,
        (Loan.permissionState_eq_iff.mp shape).2.2.2.2.2.2.2]
  | shared backing ih => exact ih recorded
  | guarded backing carrier ih =>
      obtain ⟨loan,found⟩ := recorded.2
      obtain ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
      simp only [Authority.guardLoans,ih recorded.1,found,selected,Option.map_some,Option.getD_some,
        (Loan.permissionState_eq_iff.mp shape).2.2.2.2.2.2.2]

/-- Ancestry below the frontier is genuine source ancestry: the step adds no
row under a recorded identity's parent chain. -/
theorem AncestorLoan.of_frame {before middle : World} (valid : middle.WellFormed)
    (frame : StepFrame before middle) {ancestor descendant : Identity}
    (related : AncestorLoan middle ancestor descendant) (old : descendant < before.nextLoan) :
    AncestorLoan before ancestor descendant := by
  induction related with
  | refl => exact .refl
  | @parent parent child loan found link prior ih =>
      obtain ⟨source,beforeFound,sourceShape⟩ := StepFrame.row_of_middle frame old found
      have parentEq : source.parent = some parent :=
        (Loan.permissionState_eq_iff.mp sourceShape).2.1.trans link
      obtain ⟨_,_,ordered,_,_,_⟩ := World.loanParents valid child loan parent found link
      exact .parent beforeFound parentEq (ih (Nat.lt_trans ordered old))

theorem AncestorLoan.of_stepFrame {before middle : World} (valid : before.WellFormed)
    (frame : StepFrame before middle) {ancestor descendant : Identity}
    (related : AncestorLoan before ancestor descendant) : AncestorLoan middle ancestor descendant :=
  related.retained (fun _ _ found => StepFrame.row_of_before valid frame found)

/-- One observed permission row survives the step: the queried identity is
recorded at the source world, so its row is retained and every overlapping
exclusion keeps its source ancestry. -/
theorem LoanPermission.of_frame {before middle : World} (valid : before.WellFormed)
    (middleValid : middle.WellFormed) (frame : StepFrame before middle)
    {id : Identity} {requested : Access} {address : Address}
    (bound : id < before.nextLoan) (permission : LoanPermission middle id requested address) :
    LoanPermission before id requested address := by
  obtain ⟨active,found,live,root,generation,path,mode,excluded,guards,dependent⟩ := permission
  obtain ⟨source,selected,shape⟩ := StepFrame.row_of_middle frame bound found
  have fields := Loan.permissionState_eq_iff.mp shape
  refine ⟨source,selected,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [fields.2.2.2.2.2.1]; exact live
  · rw [fields.2.2.1]; exact root
  · rw [fields.2.2.1]; exact generation
  · rw [fields.2.2.1]; exact path
  · intro nonshared; rw [fields.2.2.2.1]; exact mode nonshared
  · intro other loan present alive different overlap conflict
    obtain ⟨current,currentFound,currentShape⟩ := StepFrame.row_of_before valid frame present
    have currentFields := Loan.permissionState_eq_iff.mp currentShape
    have chain := excluded other current currentFound
      (by rw [currentFields.2.2.2.2.2.1]; exact alive) different
      (by rw [currentFields.2.2.1]; exact overlap)
      (by rw [currentFields.2.2.2.1]; exact conflict)
    exact chain.of_frame middleValid frame bound
  · intro guard member
    rw [fields.2.2.2.2.2.2.2] at member
    obtain ⟨carrier,carrierFound,carrierBound,carrierLive⟩ :=
      World.loanGuards middleValid id active guard found member
    obtain ⟨current,currentFound,currentShape⟩ :=
      StepFrame.row_of_middle frame (Nat.lt_trans carrierBound bound) carrierFound
    exact ⟨current,currentFound,
      by rw [(Loan.permissionState_eq_iff.mp currentShape).2.2.2.2.2.1]; exact carrierLive live⟩
  · intro other loan present alive member
    obtain ⟨current,currentFound,currentShape⟩ := StepFrame.row_of_before valid frame present
    have currentFields := Loan.permissionState_eq_iff.mp currentShape
    exact dependent other current currentFound (by rw [currentFields.2.2.2.2.2.1]; exact alive)
      (by rw [currentFields.2.2.2.2.2.2.2]; exact member)

/-- Every permission of a recorded authority survives the step: the authority
names only rows below the frontier, and every exclusion clause of the source
permission is re-read through the retained rows. -/
theorem Permitted.of_frame {before middle : World} (valid : before.WellFormed)
    (middleValid : middle.WellFormed) (frame : StepFrame before middle)
    {authority : Authority} {requested : Access} {address : Address}
    (recorded : authority.Recorded before.loans) (bound : address.root < before.nextRoot)
    (permission : Permitted middle authority requested address) :
    Permitted before authority requested address := by
  obtain ⟨root,selected⟩ := permission.root
  obtain ⟨source,sourceFound,_⟩ := StepFrame.root_of_middle frame bound selected
  induction authority with
  | owner =>
      refine ⟨⟨source,sourceFound⟩,?_⟩
      intro id loan found live overlap conflict
      obtain ⟨current,currentFound,currentShape⟩ := StepFrame.row_of_before valid frame found
      have currentFields := Loan.permissionState_eq_iff.mp currentShape
      exact permission.2 id current currentFound
        (by rw [currentFields.2.2.2.2.2.1]; exact live)
        (by rw [currentFields.2.2.1]; exact overlap)
        (by rw [currentFields.2.2.2.1]; exact conflict)
  | loan id =>
      obtain ⟨loan,found⟩ := recorded
      exact ⟨⟨source,sourceFound⟩,
        LoanPermission.of_frame valid middleValid frame (World.loanBounds valid found) permission.2⟩
  | shared backing ih =>
      exact ⟨⟨source,sourceFound⟩,permission.2.1,ih recorded permission.2.2⟩
  | guarded backing carrier ih =>
      obtain ⟨backingPermission,carrierLoan,carrierFound,carrierPermission⟩ := permission.2
      obtain ⟨loan,found⟩ := recorded.2
      obtain ⟨current,currentFound,currentShape⟩ :=
        StepFrame.row_of_middle frame (World.loanBounds valid found) carrierFound
      have referentEq : current.referent = carrierLoan.referent :=
        (Loan.permissionState_eq_iff.mp currentShape).2.2.1
      exact ⟨⟨source,sourceFound⟩,ih recorded.1 backingPermission,current,currentFound,
        referentEq ▸ LoanPermission.of_frame valid middleValid frame (World.loanBounds valid found) carrierPermission⟩

/-- One observed allocation claim survives the step: its anchor is recorded at
the source world, so its row, its root home and its latest-owner clause are all
re-read from the retained records. -/
theorem AllocationClaim.of_frame {before middle : World} (valid : before.WellFormed)
    (frame : StepFrame before middle)
    {authority : Authority} {address : Address} (bound : address.root < before.nextRoot)
    (anchorBound : ∀ anchor, authority.parentLoan = some anchor → anchor < before.nextLoan)
    (claim : AllocationClaim middle authority address) : AllocationClaim before authority address := by
  obtain ⟨identity,loan,root,domain,atIdentity,found,live,owning,referent,whole,selected,home,latest⟩ := claim
  obtain ⟨source,sourceFound,sourceShape⟩ :=
    StepFrame.row_of_middle frame (anchorBound identity atIdentity) found
  have fields := Loan.permissionState_eq_iff.mp sourceShape
  obtain ⟨beforeRoot,beforeFound,homeEq⟩ := StepFrame.root_of_middle frame bound selected
  refine ⟨identity,source,beforeRoot,domain,atIdentity,sourceFound,?_,?_,?_,whole,beforeFound,?_,?_⟩
  · rw [fields.2.2.2.2.2.1]; exact live
  · rw [fields.2.2.2.2.2.2.1]; exact owning
  · rw [fields.2.2.1]; exact referent
  · rw [← homeEq]; exact home
  · intro child successor present alive childOwning ancestry
    obtain ⟨current,currentFound,currentShape⟩ := StepFrame.row_of_before valid frame present
    have childFields := Loan.permissionState_eq_iff.mp currentShape
    have middleAncestry : AncestorLoan middle identity child := ancestry.of_stepFrame valid frame
    exact latest child current currentFound (by rw [childFields.2.2.2.2.2.1]; exact alive)
      (by rw [childFields.2.2.2.2.2.2.1]; exact childOwning) middleAncestry

/-- The observed claim protection of a recorded anchor survives the step: the
new row's parent is recorded, so source ancestry below it is genuine. -/
theorem Kernel.StepFrame.claimProtected {before middle : World} (middleValid : middle.WellFormed)
    (frame : StepFrame before middle)
    {parent anchor : Identity} (bound : parent < before.nextLoan)
    (protection : before.ClaimProtected .owning (some parent) anchor) :
    middle.ClaimProtected .owning (some parent) anchor := by
  refine Or.inr (fun other same related => ?_)
  have equal : parent = other := Option.some.inj same
  rw [← equal] at related
  rcases protection with notOwning | noAncestor
  · exact absurd rfl notOwning
  · exact noAncestor parent rfl (AncestorLoan.of_frame middleValid frame related bound)

/-! ## 9. The root and row frame of each actual binding rule

Every real rule changes the root table in one of exactly two ways: it installs
at most one root, at the storage frontier, or it updates the value inside an
already recorded root. `RootFrame` states that shape against one frontier and
composes over the two writes a resident handoff performs; `StepFrame` is its
instance at `before.nextRoot`. The row half is read from the actual tables. -/

namespace Kernel

/-- Internal logical homes: no allocation or external domain owns the root. -/
def InternalRoot (root : Root) : Prop :=
  ∀ domain, root.home ≠ Home.allocation domain ∧ root.home ≠ Home.external domain

theorem InternalRoot.localSlot (activation scope : Identity) :
    ∀ domain, (Home.localSlot activation scope : Home) ≠ Home.allocation domain ∧
      (Home.localSlot activation scope : Home) ≠ Home.external domain := by
  intro domain
  refine ⟨?_,?_⟩
  · intro same; cases same
  · intro same; cases same

theorem InternalRoot.temporaryHome (activation scope : Identity) :
    ∀ domain, (Home.temporary activation scope : Home) ≠ Home.allocation domain ∧
      (Home.temporary activation scope : Home) ≠ Home.external domain := by
  intro domain
  refine ⟨?_,?_⟩
  · intro same; cases same
  · intro same; cases same

theorem InternalRoot.of_home {root : Root} {home : Home} (same : root.home = home)
    (internal : ∀ domain, home ≠ Home.allocation domain ∧ home ≠ Home.external domain) :
    InternalRoot root := by
  intro domain
  exact ⟨by rw [same]; exact (internal domain).1,by rw [same]; exact (internal domain).2⟩

/-- A write outside one root leaves that root's record alone. -/
theorem StepFrame.write_roots_other {before after : World} {address : Address}
    {value : Option Value} {id : Identity} (written : before.write address value = some after)
    (outside : id ≠ address.root) : after.roots.get id = before.roots.get id := by
  obtain ⟨root,replacement,_,rfl⟩ := World.write_value_update written
  exact Table.get_set_other _ _ _ _ outside

/-- One step's root table against one frontier: every root below keeps its
location, nothing above changes, and the frontier itself carries an internal
home. -/
structure RootFrame (before middle : World) (frontier : Identity) : Prop where
  below : ∀ id, id < frontier →
    (middle.roots.get id).map Root.location = (before.roots.get id).map Root.location
  above : ∀ id, frontier < id → middle.roots.get id = before.roots.get id
  internal : ∀ root, middle.roots.get frontier = some root → InternalRoot root

theorem RootFrame.trans {before middle after : World} {frontier : Identity}
    (first : RootFrame before middle frontier) (second : RootFrame middle after frontier) :
    RootFrame before after frontier where
  below := fun id bound => (second.below id bound).trans (first.below id bound)
  above := fun id bound => (second.above id bound).trans (first.above id bound)
  internal := fun root found => second.internal root found

/-- Two worlds with the same root table: the frame is read off that table, and
the frontier is empty, so it holds at any frontier. -/
theorem RootFrame.of_roots_eq {before middle : World} {frontier : Identity}
    (roots : middle.roots = before.roots) (absent : before.roots.get frontier = none) :
    RootFrame before middle frontier where
  below := fun _ _ => by rw [roots]
  above := fun _ _ => by rw [roots]
  internal := fun root found => by rw [roots,absent] at found; cases found

/-- A frame is read through a world whose root table agrees with it. -/
theorem RootFrame.congr {before middle other : World} {frontier : Identity}
    (frame : RootFrame before middle frontier) (roots : other.roots = middle.roots) :
    RootFrame before other frontier where
  below := fun id bound => by rw [roots]; exact frame.below id bound
  above := fun id bound => by rw [roots]; exact frame.above id bound
  internal := fun root found => frame.internal root (by rw [roots] at found; exact found)

/-- One fresh allocation installs exactly the frontier root, with the home its
rule selected. -/
theorem RootFrame.of_allocates {program : Language.Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after)
    (internal : ∀ domain, home ≠ Home.allocation domain ∧ home ≠ Home.external domain) :
    RootFrame before after before.nextRoot := by
  cases allocated with
  | fresh request extent =>
    refine ⟨fun id bound => ?_,fun id bound => ?_,fun observed selected => ?_⟩
    · rw [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)]
    · rw [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound).symm]
    · rw [Table.get_set] at selected
      exact InternalRoot.of_home (by rw [(Option.some.inj selected).symm]) internal

/-- One write at the frontier: the recorded frontier root keeps its location
and the home its rule gave it. -/
theorem RootFrame.of_write_at {before after : World} {address : Address} {value : Option Value}
    {frontier : Identity} (written : before.write address value = some after)
    (rootEq : address.root = frontier)
    (internal : ∀ root, before.roots.get frontier = some root → InternalRoot root) :
    RootFrame before after frontier := by
  obtain ⟨root,replacement,found,rfl⟩ := World.write_value_update written
  refine ⟨fun id bound => ?_,fun id bound => ?_,fun observed selected => ?_⟩
  · rw [Table.get_set_other _ _ _ _ (by rw [rootEq]; exact Nat.ne_of_lt bound)]
  · rw [Table.get_set_other _ _ _ _ (by rw [rootEq]; exact (Nat.ne_of_lt bound).symm)]
  · rw [← rootEq,Table.get_set] at selected
    exact InternalRoot.of_home (by rw [(Option.some.inj selected).symm])
      (internal root (by rw [← rootEq]; exact found))

/-- One value-only write strictly below the frontier changes no location. -/
theorem RootFrame.of_write_below {before after : World} {address : Address} {value : Option Value}
    {frontier : Identity} (written : before.write address value = some after)
    (below : address.root < frontier)
    (internal : ∀ root, before.roots.get frontier = some root → InternalRoot root) :
    RootFrame before after frontier := by
  obtain ⟨root,replacement,found,rfl⟩ := World.write_value_update written
  refine ⟨fun id bound => ?_,fun id bound => ?_,fun observed selected => ?_⟩
  · by_cases same : id = address.root
    · rw [same,Table.get_set,found]
      rfl
    · rw [Table.get_set_other _ _ _ _ same]
  · rw [Table.get_set_other _ _ _ _ (Ne.symm (Nat.ne_of_lt (Nat.lt_trans below bound)))]
  · rw [Table.get_set_other _ _ _ _ (Ne.symm (Nat.ne_of_lt below))] at selected
    exact internal observed selected

/-- The record layer `StepFrame` names, assembled from the root frame and the
retained permission projection of the actual rows. -/
theorem StepFrame.of_rootFrame {before middle : World} (valid : before.WellFormed)
    (frame : RootFrame before middle before.nextRoot)
    (rows : ∀ id, id ≠ before.nextLoan →
      (middle.loans.get id).map Loan.permissionState = (before.loans.get id).map Loan.permissionState) :
    StepFrame before middle where
  retained := rows
  rooted := frame.below
  anchored := by
    intro id root found home
    by_cases below : id < before.nextRoot
    · exact below
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt below) with above | same
      · have restored := frame.above id above
        rw [restored] at found
        exact absurd (World.root_bound valid found) (Nat.not_lt.mpr (Nat.le_of_lt above))
      · have atFrontier : middle.roots.get before.nextRoot = some root := by rw [same]; exact found
        have notInternal := frame.internal root atFrontier
        rcases home with ⟨domain,sameHome⟩ | ⟨domain,sameHome⟩
        · exact absurd sameHome (notInternal domain).1
        · exact absurd sameHome (notInternal domain).2

end Kernel

/-- Both directions of one administrative table update, read as the retained
permission projection of the actual tables. -/
theorem World.RowRelation.map_permissionState {before after : World} (rows : World.RowRelation before after) :
    ∀ id, (after.loans.get id).map Loan.permissionState = (before.loans.get id).map Loan.permissionState := by
  intro id
  cases found : before.loans.get id with
  | none =>
      cases present : after.loans.get id with
      | none => rfl
      | some loan =>
          obtain ⟨source,selected,_⟩ := rows.backward id loan present
          rw [found] at selected
          cases selected
  | some original =>
      obtain ⟨current,selected,shape⟩ := rows.forward id original found
      rw [selected,Option.map_some,Option.map_some,shape]

namespace Kernel

theorem LendsResident.stepFrame {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {address : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease result after) :
    StepFrame before after := by
  cases lent with
  | owned => exact StepFrame.of_rootFrame valid (RootFrame.of_roots_eq rfl (World.freshRoot valid)) (fun _ _ => rfl)
  | lent modes stored borrowRegion allocated formed =>
    cases formed with
    | borrow _ _ _ _ _ _ _ _ _ _ written =>
      refine StepFrame.of_rootFrame valid ?_ ?_
      · refine ((RootFrame.of_allocates allocated (InternalRoot.temporaryHome activation scope)).trans
          (RootFrame.of_write_at written (Allocates.fresh_root allocated).1 ?_)).congr rfl
        intro root found
        refine InternalRoot.of_home (Allocates.created_home allocated root ?_) (InternalRoot.temporaryHome activation scope)
        rw [(Allocates.fresh_root allocated).1]
        exact found
      · intro identity apart
        rw [Table.get_set_other _ _ _ _ (by rw [Allocates.nextLoan allocated]; exact apart),Allocates.loans allocated]


theorem BindsInputAt.stepFrame {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before middle : World} {input : InvocationInput}
    {binding : Binding} (valid : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding middle) :
    StepFrame before middle := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact lent.stepFrame valid
  | owned ready owning resident stored type allocProof transferred =>
    cases transferred with
    | move sourceStored initialized moveReady permitted vacant separated destinationType clear install =>
      have below : input.storage.root < before.nextRoot := by
        obtain ⟨root,selected,_⟩ := Option.bind_eq_some_iff.mp stored
        exact World.root_bound valid (World.root_found selected).1
      refine StepFrame.of_rootFrame valid ?_ ?_
      · refine ((RootFrame.of_allocates allocProof
            (InternalRoot.localSlot activation scope)).trans
          ((RootFrame.of_write_below clear below ?_).trans
            (RootFrame.of_write_at install (Allocates.fresh_root allocProof).1 ?_)))
        · intro root found
          refine InternalRoot.of_home (Allocates.created_home allocProof root ?_)
            (InternalRoot.localSlot activation scope)
          rw [(Allocates.fresh_root allocProof).1]
          exact found
        · intro root found
          have apart : before.nextRoot ≠ input.storage.root := (Nat.ne_of_lt below).symm
          rw [StepFrame.write_roots_other clear apart] at found
          refine InternalRoot.of_home (Allocates.created_home allocProof root ?_)
            (InternalRoot.localSlot activation scope)
          rw [(Allocates.fresh_root allocProof).1]
          exact found
      · intro id _
        rw [World.write_loans install,World.write_loans clear,Allocates.loans allocProof]
  | storage ready formal locatedType claimed =>
    cases claimed with
    | claim rootFound located permitted =>
      refine StepFrame.of_rootFrame valid (RootFrame.of_roots_eq rfl (World.freshRoot valid)) ?_
      intro id apart
      rw [Table.get_set_other _ _ _ _ apart]
  | allocation ready formal owning locatedType transferred =>
    refine StepFrame.of_rootFrame valid
      (RootFrame.of_roots_eq (Glorious.Language.TransfersAllocation.roots_eq transferred) (World.freshRoot valid)) ?_
    intro id _
    exact World.RowRelation.map_permissionState (Glorious.Language.TransfersAllocation.row_relation transferred) id
  | guardedAllocation ready formal owning guarded locatedType claimed =>
    cases claimed with
    | claim owning permitted selected =>
      refine StepFrame.of_rootFrame valid (RootFrame.of_roots_eq rfl (World.freshRoot valid)) ?_
      intro id apart
      rw [Table.get_set_other _ _ _ _ apart]
  | loan ready formal owning locatedType transferred =>
    refine StepFrame.of_rootFrame valid
      (RootFrame.of_roots_eq (Glorious.Language.TransfersStorageLoan.roots_eq transferred) (World.freshRoot valid)) ?_
    intro id _
    exact World.RowRelation.map_permissionState (Glorious.Language.TransfersStorageLoan.row_relation transferred) id

end Kernel

/-! ## 10. Write-local storage projections for the resident rules

A resident handoff writes at the storage frontier and, for an owned formal,
clears the source it moves. Both are outside the storage of every other input
of the batch, so the projected read graph of that input is unchanged; the
lemmas below state the projection once per write. -/

theorem Address.not_properPrefix_of_root_ne {ancestor descendant : Address}
    (apart : ancestor.root ≠ descendant.root) : ¬ ancestor.ProperPrefix descendant :=
  fun included => apart included.1.1

theorem Address.not_properPrefix_of_not_overlaps {ancestor descendant : Address}
    (apart : ¬ ancestor.Overlaps descendant) : ¬ ancestor.ProperPrefix descendant :=
  fun included => apart ⟨included.1.1,included.1.2.1,Or.inr included.1.2.2⟩

/-- A disjoint write does not change whether the observed address stores a
value, in either direction. -/
theorem World.Stores.write_disjoint_iff {before after : World} {mutation address : Address}
    {mutationValue : Option Value} (written : before.write mutation mutationValue = some after)
    (apart : ¬ mutation.Overlaps address) {resident : Value} :
    before.Stores address resident ↔ after.Stores address resident := by
  have framed : after.read address = before.read address := World.write_disjoint written apart
  constructor
  · intro stored
    rw [World.Stores] at stored ⊢
    rw [framed]
    exact stored
  · intro stored
    rw [World.Stores] at stored ⊢
    rw [← framed]
    exact stored

/-- A fresh allocation changes no read at all. -/
theorem Allocates.stores_iff {program : Program} {before after : World}
    {home region type layout mutable address} {originBound : Identity}
    (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after)
    {address : Address} {resident : Value} :
    before.Stores address resident ↔ after.Stores address resident := by
  have framed : after.read address = before.read address := allocated.read valid address
  constructor
  · intro stored
    rw [World.Stores] at stored ⊢
    rw [framed]
    exact stored
  · intro stored
    rw [World.Stores] at stored ⊢
    rw [← framed]
    exact stored

/-- A disjoint write preserves locatedness of the observed address. -/
theorem World.Located.write_disjoint {before after : World} {mutation address : Address}
    {mutationValue : Option Value} (written : before.write mutation mutationValue = some after)
    (apart : ¬ mutation.Overlaps address) (located : before.Located address) : after.Located address :=
  World.write_located written (Address.not_properPrefix_of_not_overlaps apart) located

/-- A write at a different root leaves the observed read alone. -/
theorem World.read_root_other {before after : World} {mutation address : Address}
    {mutationValue : Option Value} (written : before.write mutation mutationValue = some after)
    (apart : address.root ≠ mutation.root) : after.read address = before.read address := by
  obtain ⟨root,replacement,found,rfl⟩ := World.write_value_update written
  simp only [World.read,World.root]
  rw [Table.get_set_other _ _ _ _ apart]

theorem World.Stores.root_other {before after : World} {mutation address : Address}
    {mutationValue : Option Value} (written : before.write mutation mutationValue = some after)
    (apart : address.root ≠ mutation.root) {resident : Value} :
    before.Stores address resident ↔ after.Stores address resident := by
  have framed : after.read address = before.read address := World.read_root_other written apart
  constructor
  · intro stored
    rw [World.Stores] at stored ⊢
    rw [framed]
    exact stored
  · intro stored
    rw [World.Stores] at stored ⊢
    rw [← framed]
    exact stored

theorem World.Vacant.root_other {before after : World} {mutation address : Address}
    {mutationValue : Option Value} (written : before.write mutation mutationValue = some after)
    (apart : address.root ≠ mutation.root) (vacant : before.Vacant address) : after.Vacant address := by
  obtain ⟨root,selected,shape⟩ := vacant
  have framed : after.root address = before.root address := by
    obtain ⟨writtenRoot,replacement,writtenFound,rfl⟩ := World.write_value_update written
    simp only [World.root]
    rw [Table.get_set_other _ _ _ _ apart]
  refine ⟨root,?_,shape⟩
  rw [framed]
  exact selected

theorem World.Located.root_other {before after : World} {mutation address : Address}
    {mutationValue : Option Value} (written : before.write mutation mutationValue = some after)
    (apart : address.root ≠ mutation.root) (located : before.Located address) : after.Located address := by
  rcases located with ⟨resident,stored⟩ | vacant
  · exact Or.inl ⟨resident,(World.Stores.root_other written apart).mp stored⟩
  · exact Or.inr (World.Vacant.root_other written apart vacant)



/-! ## 11. Pending-tail transport

The tail of the ordered batch must see the same product after one head binding.
Every channel is read from the source world through the actual step: the graph
is an equivalence with identical view labels, the row is re-read from the
retained source row, and every permission is pulled back with the record layer
of the step. -/

namespace Kernel

/-- One recorded authority's compatibility with a fresh row survives the step:
the carrier row lies below the loan frontier, so its referent is re-read from
the retained source row. -/
theorem Authority.LoanCompatible.frame {before middle : World} (valid : before.WellFormed)
    (frame : StepFrame before middle) {authority : Authority} (recorded : authority.Recorded before.loans)
    {requested : Access} {address referent : Address} {mode : Mutability} {guards : List Identity}
    (compatible : authority.LoanCompatible before requested address referent mode guards) :
    authority.LoanCompatible middle requested address referent mode guards := by
  induction authority with
  | owner => exact compatible
  | loan identity => exact compatible
  | shared backing ih => exact ih recorded compatible
  | guarded backing carrier ih =>
      obtain ⟨carrierLoan,carrierFound⟩ := recorded.2
      refine ⟨ih recorded.1 compatible.1,fun loan selected => ?_⟩
      obtain ⟨source,sourceFound,shape⟩ :=
        StepFrame.row_of_middle frame (World.loanBounds valid carrierFound) selected
      have referentEq : loan.referent = source.referent := (Loan.permissionState_eq_iff.mp shape).2.2.1.symm
      refine ⟨fun overlap => (compatible.2 source sourceFound).1 ?_,
        fun member => (compatible.2 source sourceFound).2 member⟩
      rw [referentEq] at overlap
      exact overlap

/-- The fresh row one head inserts is already read from the source world: only
its inherited guard list changes with the world, and the head's authority is
recorded. -/
theorem InvocationInput.FreshRow.frame {before middle : World} (valid : before.WellFormed)
    (frame : StepFrame before middle) {head : InvocationInput} (recorded : head.authority.Recorded before.loans)
    {referent : Address} {mode : Mutability} {guards : List Identity} {kind : LoanKind}
    (fresh : head.FreshRow middle referent mode guards kind) : head.FreshRow before referent mode guards kind := by
  have guardsEq : head.authority.guardLoans middle = head.authority.guardLoans before :=
    StepFrame.guards valid frame recorded
  cases formal : head.formal with
  | resident localSlot =>
      simp only [InvocationInput.FreshRow,formal] at fresh ⊢
      exact ⟨fresh.1,fresh.2.1,fresh.2.2.1,fresh.2.2.2.1,fresh.2.2.2.2.trans guardsEq⟩
  | storage identity type =>
      simp only [InvocationInput.FreshRow,formal] at fresh ⊢
      exact ⟨fresh.1,fresh.2.1,fresh.2.2.1,fresh.2.2.2.trans guardsEq⟩
  | allocation identity type =>
      simp only [InvocationInput.FreshRow,formal] at fresh ⊢
      exact ⟨fresh.1,fresh.2.1,fresh.2.2.1,fresh.2.2.2.1,fresh.2.2.2.2.trans guardsEq⟩
  | loan identity type =>
      simp only [InvocationInput.FreshRow,formal] at fresh ⊢

/-- A custody write the head performs is one of its own already recorded rows. -/
theorem InvocationInput.CustodyMoved.frame {before middle : World} (valid : before.WellFormed)
    (frame : StepFrame before middle) {head : InvocationInput} (recorded : head.authority.Recorded before.loans)
    {identity : Identity} (moved : head.CustodyMoved middle identity) : head.CustodyMoved before identity := by
  rcases moved with ⟨obligation,type,formal,authorityAt⟩ | ⟨obligation,type,formal,authorityAt,loan,found,mode⟩
  · exact Or.inl ⟨obligation,type,formal,authorityAt⟩
  · obtain ⟨carrierLoan,carrierFound⟩ := recorded.parentLoan (by rw [authorityAt]; rfl)
    obtain ⟨source,sourceFound,shape⟩ :=
      StepFrame.row_of_middle frame (World.loanBounds valid carrierFound) found
    exact Or.inr ⟨obligation,type,formal,authorityAt,source,sourceFound,
      (Loan.permissionState_eq_iff.mp shape).2.2.2.1.trans mode⟩

/-- One observed permission view of a value is read back from the source world:
the reachable graph is an equivalence with identical labels, and the row's
referent and mode are retained. -/
theorem Value.ObservedViews.backward {before middle : World} {value : Value} {access : Access}
    (batch : value.BatchCompatible before middle) (framed : value.SupportFramed before middle)
    {authority : Authority} {requested : Access} {address : Address}
    (observed : value.ObservedViews middle access authority requested address) :
    value.ObservedViews before access authority requested address := by
  rcases observed with
    ⟨identity,current,viewAccess,loan,reached,found,atAuthority,atRequested,atAddress⟩ |
    ⟨residentValue,current,incoming,binding,reached,member,atAuthority,atRequested,atAddress⟩
  · obtain ⟨carrier,reachable,head⟩ := reached
    obtain ⟨beforeCarrier,beforeReachable,beforeHead⟩ :=
      (Value.ReachableReference.frame_batch (authority := .owner) batch framed).mpr
        ⟨carrier,reachable,head⟩
    obtain ⟨original,originalFound,shape⟩ :=
      batch.rows.selected_before ⟨beforeCarrier,beforeReachable,beforeHead⟩ found
    have fields := Loan.permissionState_eq_iff.mp shape
    refine Or.inl ⟨identity,current,viewAccess,original,⟨beforeCarrier,beforeReachable,beforeHead⟩,
      originalFound,?_,?_,?_⟩
    · rw [atAuthority,← fields.2.2.2.1]
    · rw [atRequested,← fields.2.2.2.1]
    · rw [atAddress,← fields.2.2.1]
  · have beforeReached : value.ReachableResident before .owner access residentValue current incoming :=
      (Value.ReachableResident.frame_batch (authority := .owner) batch framed).mpr reached
    refine Or.inr ⟨residentValue,current,incoming,binding,beforeReached,member,?_,?_,?_⟩
    · exact atAuthority
    · exact atRequested
    · exact atAddress

/-- Fresh physical allocation discharges the handle-write exclusions. The
only graph compatibility premise is read in the original caller world, before
allocating the handle or forming its loan; all loan purposes use this producer. -/
theorem _root_.Glorious.Language.Execution.Temporary.borrowed_handle_ready
    {program : Kernel.Program} {before allocated after : World} {purpose : LoanPurpose}
    {context : Execution.Context} {mode : Mutability} {region : Identity} {value : Value}
    {referent handle : Address} {authority : Authority}
    (valid : before.WellFormed) (stored : before.Stores referent value)
    (ready : value.ResourcesAccessible program before (if mode = .shared then .shared else .unique))
    (temporary : Execution.Temporary program context (.reference mode (.runtimeRegion region) value.type) before handle allocated)
    (borrowed : FormsLoan program purpose allocated authority mode region referent handle after)
    (compatible : value.ViewsLoanCompatible before (if mode = .shared then .shared else .unique)
      referent mode (authority.guardLoans before)) :
    ∃ type, after.Stores handle (.resident allocated.nextOwner (.reference mode (.runtimeRegion region) type)
      (.reference allocated.nextLoan) true []) ∧
      (Value.resident allocated.nextOwner (.reference mode (.runtimeRegion region) type)
        (.reference allocated.nextLoan) true []).Initialized ∧
      (Value.resident allocated.nextOwner (.reference mode (.runtimeRegion region) type)
        (.reference allocated.nextLoan) true []).ResourcesAccessible program after .owned := by
  obtain ⟨layout,allocation⟩ := temporary
  have fresh := (Allocates.fresh_root allocation).1
  have frame := allocation.supportFramed valid ready
  have batch := Value.BatchCompatible.of_eq (allocation.locationExtension valid) allocation.loans (value := value)
  apply borrowed.handed_off_ready (allocation.wellFormed valid) ((allocation.read valid referent).trans stored)
  · intro overlap
    exact (Nat.ne_of_lt (stored.rooted_bound valid)) (overlap.1.symm.trans fresh)
  · intro observed supported overlap
    have prior := (Value.Support.frame allocation.loans frame).mpr supported
    exact (Nat.ne_of_lt (Value.Support.root_bound valid ready prior)) (overlap.1.symm.trans fresh)
  · intro query requested observed views
    rw [Authority.guardLoans.loans_congr allocation.loans]
    exact Authority.LoanCompatible.loans_congr allocation.loans
      (compatible query requested observed (Value.ObservedViews.backward batch frame views))


/-- Every authority one pending input's permission reading names is recorded in
the source world, so its compatibility is re-read from the source rows. -/
theorem InvocationInput.ReadsPermission.recorded {world : World}
    {other : InvocationInput} (recorded : other.authority.Recorded world.loans)
    (resident : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      world.Stores other.storage value → value.ResourcesRecorded world)
    {authority : Authority} {access : Access} {address : Address}
    (reads : other.ReadsPermission world authority access address) : authority.Recorded world.loans := by
  rcases reads with ⟨authorityEq,_,_⟩ | ⟨localSlot,value,formal,stored,views⟩
  · rw [authorityEq]; exact recorded
  · rcases views with
      ⟨identity,current,viewAccess,loan,reached,found,atAuthority,_,_⟩ |
      ⟨residentValue,current,incoming,binding,reached,member,atAuthority,_,_⟩
    · obtain ⟨carrier,carrierReached,head⟩ := reached
      have currentRecorded := carrierReached.recorded (authority := .owner)
        (resident localSlot value formal stored) trivial
      rw [atAuthority]
      exact currentRecorded.referenceView found (ReferenceAccess viewAccess loan.mode)
    · have currentRecorded := reached.recorded (authority := .owner)
        (resident localSlot value formal stored) trivial
      obtain ⟨bnode,baccess,breached⟩ := reached.rebase .owner .shared
      rw [atAuthority]
      exact currentRecorded.resourceView
        (resident localSlot value formal stored residentValue bnode baccess breached binding member) incoming

theorem InvocationInput.ReadsClaim.recorded {world : World} {other : InvocationInput}
    (recorded : other.authority.Recorded world.loans)
    (resident : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      world.Stores other.storage value → value.ResourcesRecorded world)
    {authority : Authority} {address : Address}
    (reads : other.ReadsClaim world authority address) : authority.Recorded world.loans := by
  rcases reads with ⟨authorityEq,_,_⟩ | ⟨localSlot,value,formal,stored,claims⟩
  · rw [authorityEq]; exact recorded
  · obtain ⟨residentValue,current,incoming,reached,binding,member,atAuthority,atAddress⟩ := claims
    rw [atAuthority]
    exact (resident localSlot value formal stored) residentValue current incoming reached binding member

theorem InvocationInput.ReadsPermission.backward {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before middle : World} {other : InvocationInput}
    (valid : before.WellFormed) (middleValid : middle.WellFormed) (frame : StepFrame before middle)
    (observation : StepObservation program footprint region before middle other)
    (recorded : other.authority.Recorded before.loans) (bound : other.storage.root < before.nextRoot)
    {authority : Authority} {access : Access} {address : Address}
    (reads : other.ReadsPermission middle authority access address) :
    other.ReadsPermission before authority access address := by
  rcases reads with ⟨authorityEq,addressEq,observed,permission⟩ | ⟨localSlot,value,formal,stored,views⟩
  · subst authority
    subst address
    exact Or.inl ⟨rfl,rfl,observed,Permitted.of_frame valid middleValid frame recorded bound permission⟩
  · have storedBefore := observation.storesBack (by rw [formal]; trivial) value stored
    obtain ⟨batch,framed⟩ := observation.value localSlot value formal storedBefore
    exact Or.inr ⟨localSlot,value,formal,storedBefore,
      Value.ObservedViews.backward batch framed views⟩

theorem InvocationInput.ReadsClaim.backward {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before middle : World} {other : InvocationInput}
    (valid : before.WellFormed) (frame : StepFrame before middle)
    (observation : StepObservation program footprint region before middle other)
    (recorded : other.authority.Recorded before.loans) (bound : other.storage.root < before.nextRoot)
    {authority : Authority} {address : Address}
    (reads : other.ReadsClaim middle authority address) : other.ReadsClaim before authority address := by
  rcases reads with ⟨authorityEq,addressEq,claim⟩ | ⟨localSlot,value,formal,stored,claims⟩
  · subst authority
    subst address
    refine Or.inl ⟨rfl,rfl,AllocationClaim.of_frame valid frame bound ?_ claim⟩
    intro anchor atAnchor
    obtain ⟨loan,found⟩ := recorded.parentLoan atAnchor
    exact World.loanBounds valid found
  · have storedBefore := observation.storesBack (by rw [formal]; trivial) value stored
    obtain ⟨batch,framed⟩ := observation.value localSlot value formal storedBefore
    obtain ⟨residentValue,current,incoming,reached,binding,member,atAuthority,atAddress⟩ := claims
    exact Or.inr ⟨localSlot,value,formal,storedBefore,
      ⟨residentValue,current,incoming,
        (Value.ReachableResident.frame_batch (authority := .owner) batch framed).mpr reached,
        binding,member,atAuthority,atAddress⟩⟩

theorem InvocationInput.ReadsCustody.backward {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before middle : World} {other : InvocationInput}
    (observation : StepObservation program footprint region before middle other)
    {authority : Authority} (reads : other.ReadsCustody middle authority) :
    other.ReadsCustody before authority := by
  rcases reads with authorityEq | ⟨localSlot,value,formal,stored,custody⟩
  · exact Or.inl authorityEq
  · have storedBefore := observation.storesBack (by rw [formal]; trivial) value stored
    obtain ⟨batch,framed⟩ := observation.value localSlot value formal storedBefore
    obtain ⟨residentValue,current,incoming,reached,binding,member,atAuthority⟩ := custody
    exact Or.inr ⟨localSlot,value,formal,storedBefore,
      ⟨residentValue,current,incoming,
        (Value.ReachableResident.frame_batch (authority := .owner) batch framed).mpr reached,
        binding,member,atAuthority⟩⟩

theorem InvocationInput.RetainsSupport.backward {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before middle : World} {other : InvocationInput}
    (observation : StepObservation program footprint region before middle other)
    {address : Address} (retained : other.RetainsSupport middle address) :
    other.RetainsSupport before address := by
  obtain ⟨localSlot,value,formal,stored,supported⟩ := retained
  have storedBefore := observation.storesBack (by rw [formal]; trivial) value stored
  obtain ⟨batch,framed⟩ := observation.value localSlot value formal storedBefore
  exact ⟨localSlot,value,formal,storedBefore,
    (Value.Support.frame_batch batch framed).mpr supported⟩

end Kernel

/-! ## 12. Transport of the pairwise independence product

One head binding is observed by the whole batch, so the product that constrains
the remaining heads against every other input is re-established in the middle
world from the source-world product and the actual step. Each channel is
re-read from the source world and then transported forward through the step's
record layer; nothing is assumed about the middle world. -/

namespace Kernel

theorem InvocationInput.IndependentOf.frame {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before middle : World} {head other : InvocationInput}
    (valid : before.WellFormed) (middleValid : middle.WellFormed) (frame : StepFrame before middle)
    (observation : StepObservation program footprint region before middle other)
    (headRecorded : head.authority.Recorded before.loans)
    (otherRecorded : other.authority.Recorded before.loans) (otherBound : other.storage.root < before.nextRoot)
    (otherAccessible : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesAccessible program before other.access)
    (compatible : head.IndependentOf program footprint before other) :
    head.IndependentOf program footprint middle other where
  permission := by
    intro referent mode guards kind fresh authority access address reads
    have residentRecorded : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value → value.ResourcesRecorded before :=
      fun localSlot value formal stored => (otherAccessible localSlot value formal stored).resourcesRecorded
    have readsBefore := InvocationInput.ReadsPermission.backward valid middleValid frame observation
      otherRecorded otherBound reads
    exact Authority.LoanCompatible.frame valid frame
      (InvocationInput.ReadsPermission.recorded otherRecorded residentRecorded readsBefore)
      (compatible.permission referent mode guards kind
        (InvocationInput.FreshRow.frame valid frame headRecorded fresh) authority access address readsBefore)
  claim := by
    intro parent freshOwning authority address reads claim anchor atAnchor
    have residentRecorded : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value → value.ResourcesRecorded before :=
      fun localSlot value formal stored => (otherAccessible localSlot value formal stored).resourcesRecorded
    have readsBefore := InvocationInput.ReadsClaim.backward valid frame observation otherRecorded otherBound reads
    have authorityRecorded := InvocationInput.ReadsClaim.recorded otherRecorded residentRecorded readsBefore
    have claimBound : address.root < before.nextRoot := by
      obtain ⟨identity,loan,root,domain,atIdentity,found,live,owning,referent,whole,selected,home,latest⟩ := claim
      exact frame.anchored address.root root (World.root_found selected).1
        (home.elim (fun same => Or.inl ⟨domain,same⟩) (fun same => Or.inr ⟨domain,same⟩))
    have claimBefore : AllocationClaim before authority address := by
      refine AllocationClaim.of_frame valid frame claimBound ?_ claim
      intro anchor atAnchor
      obtain ⟨loan,found⟩ := authorityRecorded.parentLoan atAnchor
      exact World.loanBounds valid found
    have parentBound : parent < before.nextLoan := by
      obtain ⟨_,atParent⟩ := freshOwning
      obtain ⟨loan,found⟩ := headRecorded.parentLoan atParent
      exact World.loanBounds valid found
    exact StepFrame.claimProtected middleValid frame parentBound
      (compatible.claim parent freshOwning authority address readsBefore claimBefore anchor atAnchor)
  custody := by
    intro identity moved authority reads
    exact compatible.custody identity (InvocationInput.CustodyMoved.frame valid frame headRecorded moved) authority
      (InvocationInput.ReadsCustody.backward observation reads)
  clear := fun address member => compatible.clear address member
  support := by
    intro address retained
    obtain ⟨localSlot,value,formal,storedBefore,supportedBefore⟩ :=
      InvocationInput.RetainsSupport.backward observation retained
    have bound : address.root < before.nextRoot := by
      obtain ⟨root,found⟩ :=
        (otherAccessible localSlot value formal storedBefore).support_root supportedBefore
      exact World.root_bound valid (World.root_found found).1
    have middleBound : address.root < middle.nextRoot := Nat.lt_of_lt_of_le bound observation.nextRootBound
    intro overlap
    exact (Nat.ne_of_lt middleBound) overlap.1.symm

end Kernel


/-- Every rule that only inserts or rewrites loan rows leaves the storage
frontier alone, so a frontend that needs the middle frontier reads it here. -/
theorem FormsLoan.nextRoot {purpose : LoanPurpose} {program : RuntimeProgram} {before after : World}
    {authority : Authority} {mode : Mutability} {region : Identity} {referent destination : Address}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    after.nextRoot = before.nextRoot := by
  cases borrowed with
  | borrow _ _ _ _ _ _ _ _ _ _ written =>
      obtain ⟨root,replacement,found,rfl⟩ := World.write_value_update written
      rfl

theorem ClaimsStorage.nextRoot {custody : ClaimCustody} {before after : World}
    {authority : Authority} {access : Access} {address : Address} {created : Identity}
    (claimed : ClaimsStorage custody before authority access address created after) :
    after.nextRoot = before.nextRoot := by cases claimed; rfl

theorem ClaimsAllocation.nextRoot {custody : ClaimCustody} {before after : World}
    {authority : Authority} {address : Address} {created : Identity}
    (claimed : ClaimsAllocation custody before authority address created after) :
    after.nextRoot = before.nextRoot := by cases claimed; rfl

theorem TransfersAllocation.nextRoot {recipient : ClaimCustody} {before after : World} {place : ResolvedPlace}
    (moved : TransfersAllocation recipient before place after) :
    after.nextRoot = before.nextRoot := by cases moved; rfl

theorem TransfersStorageLoan.nextRoot {recipient : ClaimCustody} {before after : World} {place : ResolvedPlace}
    (moved : TransfersStorageLoan recipient before place after) :
    after.nextRoot = before.nextRoot := by cases moved <;> rfl

/-! ## 13. The pre-state facts of one pending input

A later binding observes a still-pending input through three facts read from
the current world: the authority that input carries is a recorded row below
the loan frontier, its storage lies below the storage frontier, and, when it is
a resident, the value stored at that storage has an accessible source graph.
These are exactly the hypotheses the six-rule observation producer consumes. -/

namespace Kernel

/-- The three facts one still-pending input needs at the current world. -/
def InputFramed (program : RuntimeProgram) (world : World) (input : InvocationInput) : Prop :=
  input.authority.Recorded world.loans ∧ input.storage.root < world.nextRoot ∧
  (∀ (localSlot : Local) (value : Value), input.formal = .resident localSlot →
    world.Stores input.storage value → value.ResourcesAccessible program world input.access)

theorem InvocationInput.ReadyFor.root_exists {program : RuntimeProgram} {world : World}
    {footprint : List Address} {input : InvocationInput} (ready : input.ReadyFor program world footprint) :
    ∃ root, world.root input.storage = some root := by
  cases input with
  | mk origin formal storage authority access =>
    cases formal with
    | resident localSlot =>
      obtain ⟨value,stored,initialized,type,handoff,permission⟩ := ready
      exact permission.root
    | storage identity type => exact ready.2.2.root
    | allocation identity type => exact ready.2.1.root_exists
    | loan identity type => exact ready.2.1.root_exists

/-- The ordinary readiness product already gives the stored-value graph and
its physical root. Only original historical authority provenance is separate;
raw loan readiness alone does not justify arbitrary carrier records. -/
theorem InputFramed.of_readyFor {program : RuntimeProgram} {world : World}
    {footprint : List Address} {input : InvocationInput} (valid : world.WellFormed)
    (ready : input.ReadyFor program world footprint) (recorded : input.authority.Recorded world.loans) :
    InputFramed program world input := by
  obtain ⟨root,found⟩ := ready.root_exists
  refine ⟨recorded,World.root_bound valid (World.root_found found).1,?_⟩
  intro localSlot value formal stored
  exact (InvocationInput.ReadyFor.resident ready (by rw [formal]; trivial) stored).2.2.1.1

theorem InvocationInputsCompatible.inputFramed {program : RuntimeProgram} {world : World}
    {footprint : List Address} {region : Identity} {inputs : List InvocationInput}
    (valid : world.WellFormed) (product : InvocationInputsCompatible program footprint region world inputs) :
    ∀ input ∈ inputs, InputFramed program world input :=
  fun input member => InputFramed.of_readyFor valid (product.ready.2.2 input member).1 (product.recorded input member)


/-- Every pending input fact is retained by one actual binding step: the row
is retained below the loan frontier, the storage frontier only grows, and the
stored value's graph is framed by the observation. -/
theorem InputFramed.frame {program : RuntimeProgram} {footprint : List Address} {region : Identity}
    {before middle : World} {other : InvocationInput}
    (observation : StepObservation program footprint region before middle other)
    (facts : InputFramed program before other) : InputFramed program middle other := by
  refine ⟨?_,?_,?_⟩
  · exact facts.1.transport (fun identity loan found =>
      let ⟨current,selected,_⟩ := observation.loans identity loan found
      ⟨current,selected⟩)
  · exact Nat.lt_of_lt_of_le facts.2.1 observation.nextRootBound
  · intro localSlot value formal stored
    have prior := observation.storesBack (by rw [formal]; trivial) value stored
    exact Value.ResourcesAccessible.frame_input (observation.value localSlot value formal prior).1
      (observation.value localSlot value formal prior).2
      (observation.framePermitted localSlot value formal prior) (facts.2.2 localSlot value formal prior)

/-- The support graph of a value is read from the world's root table alone, so
any step that keeps the root table frames it. -/
theorem Value.SupportFramed.of_roots {before after : World} (roots : after.roots = before.roots)
    {value : Value} : value.SupportFramed before after := by
  intro address _
  exact ⟨by simp only [World.read,World.root,roots],by simp only [roots]⟩

/-- The row one storage claim inserts at the loan frontier. -/
abbrev storageClaimRow (before : World) (input : InvocationInput) (root : Root)
    (recipient : ClaimCustody) : Loan :=
  ⟨before.nextLoan,input.authority.parentLoan,input.storage,
    (if input.access = .shared then .shared else .unique),root.region,true,.storageBorrow,
    input.authority.guardLoans before,false,some recipient⟩

/-- The world one storage claim produces: a single fresh row at the frontier. -/
abbrev storageClaimWorld (before : World) (input : InvocationInput) (root : Root)
    (recipient : ClaimCustody) : World :=
  { before with
    loans := before.loans.set before.nextLoan (storageClaimRow before input root recipient)
    nextLoan := before.nextLoan+1 }

/-- The observation of a step that only claims an erased storage port: one
fresh storage-borrow row at the loan frontier, no write and no root. -/
theorem StepObservation.of_storageClaim {program : RuntimeProgram} {recipient : ClaimCustody}
    {region : Identity} {before after : World} {input : InvocationInput} {footprint : List Address}
    {other : InvocationInput} {identity : Identity} {type : Term} {created : Identity}
    (valid : before.WellFormed) (frame : StepFrame before after)
    (formal : input.formal = .storage identity type)
    (claimed : ClaimsStorage recipient before input.authority input.access input.storage created after)
    (independent : input.IndependentOf program footprint before other)
    (otherAccessible : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesAccessible program before other.access) :
    StepObservation program footprint region before after other := by
  have nextRootEq := ClaimsStorage.nextRoot claimed
  have regionState := Glorious.Language.ClaimsStorage.region_state claimed
  cases claimed with
  | claim rootFound located permitted =>
    rename_i root
    let world := storageClaimWorld before input root recipient
    change StepObservation program footprint region before world other
    have loans : world.loans = before.loans.set before.nextLoan
        (storageClaimRow before input root recipient) := rfl
    have fresh : input.FreshRow before input.storage
        (if input.access = .shared then .shared else .unique) (input.authority.guardLoans before)
        .storageBorrow := by
      simp only [InvocationInput.FreshRow,formal,and_self]
    have bound : ∀ p, (storageClaimRow before input root recipient).parent = some p →
        p < before.nextLoan := by
      intro p same
      exact Permitted.parentLoan_bound valid permitted p same
    have locationsEq := Glorious.Language.World.LocationExtension.of_roots
      (before := before) (after := world) rfl
    have permittedChannel : ∀ authority access address, other.ReadsPermission before authority access address →
        Permitted before authority access address → Permitted world authority access address := by
      intro authority access address reads permission
      exact (Permitted.fresh_loan_iff (before := before) (after := world) valid locationsEq loans
        permission).mpr
        (fun _ => independent.permission input.storage
          (if input.access = .shared then .shared else .unique)
          (input.authority.guardLoans before) .storageBorrow fresh authority access address reads)
    have claimChannel : ∀ authority address, other.ReadsClaim before authority address →
        AllocationClaim before authority address → AllocationClaim world authority address := by
      intro authority address _ held
      obtain ⟨anchor,claimLoan,claimRoot,claimDomain,atAnchor,claimFound,claimLive,claimKind,
        claimReferent,claimWhole,claimSelected,claimHome,claimLatest⟩ := held
      exact AllocationClaim.fresh_loan_nonowning (before := before) (after := world) valid locationsEq loans
        ⟨anchor,claimLoan,claimRoot,claimDomain,atAnchor,claimFound,claimLive,claimKind,
          claimReferent,claimWhole,claimSelected,claimHome,claimLatest⟩ atAnchor bound
        (fun same => by cases same)
    have compatibleChannel : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value → value.BatchCompatible before world := by
      intro localSlot value formal stored
      exact Value.BatchCompatible.of_fresh_loan (before := before) (after := world) valid locationsEq loans
        ((otherAccessible localSlot value formal stored).2.1) bound
        (fun _ _ _ _ _ _ => Or.inl (fun same => by cases same))
    have framePermittedChannel : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value → value.FramePermitted before world other.access := by
      intro localSlot value formal stored authority requested address views permission
      exact (Permitted.fresh_loan_iff (before := before) (after := world) valid locationsEq loans
        permission).mpr
        (fun _ => independent.permission input.storage
          (if input.access = .shared then .shared else .unique)
          (input.authority.guardLoans before) .storageBorrow fresh authority requested address
          (Or.inr ⟨localSlot,value,formal,stored,views⟩))
    exact Glorious.Language.Kernel.StepObservation.of_loans (middle := world) rfl
      (Nat.le_of_eq nextRootEq.symm) (.of_eq regionState.1 regionState.2)
      (fun id loan found => StepFrame.row_of_before valid frame found)
      (fun id loan found =>
        let ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
        ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩)
      permittedChannel claimChannel compatibleChannel
      (fun _ _ _ _ => Value.SupportFramed.of_roots rfl) framePermittedChannel

/-- The row one guarded-allocation claim inserts at the loan frontier. -/
abbrev guardedClaimRow (before : World) (input : InvocationInput) (root : Root)
    (recipient : ClaimCustody) : Loan :=
  ⟨before.nextLoan,input.authority.parentLoan,input.storage,.unique,root.region,true,.owning,
    input.authority.guardLoans before,false,some recipient⟩

/-- The world one guarded-allocation claim produces. -/
abbrev guardedClaimWorld (before : World) (input : InvocationInput) (root : Root)
    (recipient : ClaimCustody) : World :=
  { before with
    loans := before.loans.set before.nextLoan (guardedClaimRow before input root recipient)
    nextLoan := before.nextLoan+1 }

/-- The world one whole-allocation custody handoff produces. -/
abbrev custodyUpdate (before : World) (identity : Identity) (replacement : Loan) : World :=
  { before with loans := before.loans.set identity replacement }

/-- The observation of a step that claims a fresh owning view for an erased
allocation port: one fresh owning row at the loan frontier. -/
theorem StepObservation.of_guardedClaim {program : RuntimeProgram} {recipient : ClaimCustody}
    {region : Identity} {before after : World} {input : InvocationInput} {footprint : List Address}
    {other : InvocationInput} {identity : Identity} {type : Term} {created : Identity}
    (valid : before.WellFormed) (frame : StepFrame before after)
    (formal : input.formal = .allocation identity type) (owned : input.access = .owned)
    (guarded : ∃ backing carrier, input.authority = .guarded backing carrier)
    (claimed : ClaimsAllocation recipient before input.authority input.storage created after)
    (independent : input.IndependentOf program footprint before other)
    (otherAccessible : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesAccessible program before other.access) :
    StepObservation program footprint region before after other := by
  have nextRootEq := ClaimsAllocation.nextRoot claimed
  have regionState := Glorious.Language.ClaimsAllocation.region_state claimed
  cases claimed with
  | claim claimBody permitted rootFound =>
    rename_i root
    let world := guardedClaimWorld before input root recipient
    change StepObservation program footprint region before world other
    obtain ⟨headAnchor,headLoan,headRoot,headDomain,headAtAnchor,headFound,headLive,headKind,
      headReferent,headWhole,headSelected,headHome,headLatest⟩ := claimBody
    have loans : world.loans = before.loans.set before.nextLoan
        (guardedClaimRow before input root recipient) := rfl
    have fresh : input.FreshRow before input.storage .unique (input.authority.guardLoans before)
        .owning := by
      obtain ⟨backing,carrier,authorityEq⟩ := guarded
      rw [InvocationInput.FreshRow,formal]
      exact ⟨⟨backing,carrier,authorityEq⟩,rfl,rfl,rfl,rfl⟩
    have parentBound : ∀ p, (guardedClaimRow before input root recipient).parent = some p →
        p < before.nextLoan := by
      intro p same
      exact Permitted.parentLoan_bound valid permitted p same
    have locationsEq := Glorious.Language.World.LocationExtension.of_roots
      (before := before) (after := world) rfl
    have permittedChannel : ∀ authority access address, other.ReadsPermission before authority access address →
        Permitted before authority access address → Permitted world authority access address := by
      intro authority access address reads permission
      exact (Permitted.fresh_loan_iff (before := before) (after := world) valid locationsEq loans
        permission).mpr
        (fun _ => independent.permission input.storage .unique
          (input.authority.guardLoans before) .owning fresh authority access address reads)
    have claimChannel : ∀ authority address, other.ReadsClaim before authority address →
        AllocationClaim before authority address → AllocationClaim world authority address := by
      intro authority address reads held
      obtain ⟨anchor,claimLoan,claimRoot,claimDomain,atAnchor,claimFound,claimLive,claimKind,
        claimReferent,claimWhole,claimSelected,claimHome,claimLatest⟩ := held
      have parentWitness : input.FreshOwning headAnchor := by
        obtain ⟨backing,carrier,authorityEq⟩ := guarded
        exact ⟨⟨identity,type,backing,carrier,formal,owned,authorityEq⟩,headAtAnchor⟩
      have protection := independent.claim headAnchor parentWitness authority address reads
        ⟨anchor,claimLoan,claimRoot,claimDomain,atAnchor,claimFound,claimLive,claimKind,
          claimReferent,claimWhole,claimSelected,claimHome,claimLatest⟩ anchor atAnchor
      exact AllocationClaim.fresh_loan (before := before) (after := world) valid locationsEq loans
        ⟨anchor,claimLoan,claimRoot,claimDomain,atAnchor,claimFound,claimLive,claimKind,
          claimReferent,claimWhole,claimSelected,claimHome,claimLatest⟩ atAnchor parentBound
        (by dsimp only [guardedClaimRow]; rw [headAtAnchor]; exact protection)
    have compatibleChannel : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value → value.BatchCompatible before world := by
      intro localSlot value formal' stored
      have protection : ∀ authority address, value.ObservedClaims before authority address →
          AllocationClaim before authority address → ∀ anchor, authority.parentLoan = some anchor →
            before.ClaimProtected .owning (some headAnchor) anchor := by
        intro authority address claims held anchor atAnchor
        obtain ⟨backing,carrier,authorityEq⟩ := guarded
        have parentWitness : input.FreshOwning headAnchor :=
          ⟨⟨identity,type,backing,carrier,formal,owned,authorityEq⟩,headAtAnchor⟩
        exact independent.claim headAnchor parentWitness authority address
          (Or.inr ⟨localSlot,value,formal',stored,claims⟩) held anchor atAnchor
      exact Value.BatchCompatible.of_fresh_loan (before := before) (after := world) valid locationsEq loans
        ((otherAccessible localSlot value formal' stored).2.1) parentBound
        (fun authority address claims held anchor atAnchor =>
          by dsimp only [guardedClaimRow]; rw [headAtAnchor]
             exact protection authority address claims held anchor atAnchor)
    have framePermittedChannel : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value → value.FramePermitted before world other.access := by
      intro localSlot value formal' stored authority requested address views permission
      exact (Permitted.fresh_loan_iff (before := before) (after := world) valid locationsEq loans
        permission).mpr
        (fun _ => independent.permission input.storage .unique
          (input.authority.guardLoans before) .owning fresh authority requested address
          (Or.inr ⟨localSlot,value,formal',stored,views⟩))
    exact Glorious.Language.Kernel.StepObservation.of_loans (middle := world) rfl
      (Nat.le_of_eq nextRootEq.symm) (.of_eq regionState.1 regionState.2)
      (fun id loan found => StepFrame.row_of_before valid frame found)
      (fun id loan found =>
        let ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
        ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩)
      permittedChannel claimChannel compatibleChannel
      (fun _ _ _ _ => Value.SupportFramed.of_roots rfl) framePermittedChannel

/-- The observation of a step that hands a whole-allocation custody on: one
existing row keeps its permission projection and changes only its custodian. -/
theorem StepObservation.of_allocationTransfer {program : RuntimeProgram} {recipient : ClaimCustody}
    {region : Identity} {before after : World} {input : InvocationInput} {footprint : List Address}
    {other : InvocationInput} {identity : Identity} {type : Term}
    (valid : before.WellFormed) (frame : StepFrame before after)
    (formal : input.formal = .allocation identity type) (_owned : input.access = .owned)
    (transferred : TransfersAllocation recipient before ⟨input.storage,input.authority⟩ after)
    (independent : input.IndependentOf program footprint before other)
    (otherAccessible : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesAccessible program before other.access) :
    StepObservation program footprint region before after other := by
  have nextRootEq := TransfersAllocation.nextRoot transferred
  have regionState := Glorious.Language.TransfersAllocation.region_state transferred
  have otherRestored : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.LoansRestored program before :=
    fun localSlot value formal' stored => (otherAccessible localSlot value formal' stored).2.1
  have otherReferences : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value →
      ∀ id current access, value.ReachableReference before .owner .shared id current access →
        ∃ loan, before.loans.get id = some loan :=
    fun localSlot value formal' stored id current access reached =>
      let ⟨loan,found,_⟩ := otherRestored localSlot value formal' stored id current access reached
      ⟨loan,found⟩
  cases transferred with
  | transfer authorityEq claim rowFound =>
    rename_i movedIdentity movedLoan
    have loans : (custodyUpdate before movedIdentity {movedLoan with custody := some recipient}).loans =
        before.loans.set movedIdentity {movedLoan with custody := some recipient} := rfl
    have rootEq : (custodyUpdate before movedIdentity {movedLoan with custody := some recipient}).roots =
        before.roots := rfl
    have rowRelation := World.RowRelation.of_set
      (before := before)
      (after := custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
      rowFound loans (by simp only [Loan.permissionState])
    have locationsEq := Glorious.Language.World.LocationExtension.of_roots
      (before := before) (after := custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
      rootEq
    have rootPresent : ∀ address root, before.root address = some root →
        ∃ changed, (custodyUpdate before movedIdentity {movedLoan with custody := some recipient}).root
          address = some changed :=
      fun address root found =>
        ⟨root, by
          rw [Glorious.Language.World.root_of_roots
            (before := before)
            (after := custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
            rootEq address]
          exact found⟩
    have forward : ∀ authority access address, other.ReadsPermission before authority access address →
        Permitted before authority access address →
          Permitted (custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
            authority access address :=
      fun authority access address _ permission => Permitted.of_rows rowRelation rootPresent permission
    have claimChannel : ∀ authority address, other.ReadsClaim before authority address →
        AllocationClaim before authority address →
          AllocationClaim (custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
            authority address :=
      fun authority address _ held => AllocationClaim.of_rows rowRelation locationsEq held
    have compatibleChannel : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value →
          value.BatchCompatible before
            (custodyUpdate before movedIdentity {movedLoan with custody := some recipient}) :=
      fun localSlot value formal' stored =>
        Value.BatchCompatible.of_custody_update
          (before := before)
          (after := custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
          (identity := movedIdentity) (original := movedLoan) (newCustody := recipient)
          (requested := movedLoan.returnRequested)
          locationsEq rowFound loans
          (Or.inr (Or.inr (fun resident authority access reached binding member =>
            independent.custody movedIdentity (Or.inl ⟨identity,type,formal,authorityEq⟩) binding.authority
              (Or.inr ⟨localSlot,value,formal',stored,
                ⟨resident,authority,access,reached,binding,member,rfl⟩⟩))))
    have framePermittedChannel : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value →
          value.FramePermitted before
            (custodyUpdate before movedIdentity {movedLoan with custody := some recipient}) other.access :=
      fun localSlot value formal' stored authority requested address views permission =>
        forward authority requested address (Or.inr ⟨localSlot,value,formal',stored,views⟩) permission
    exact Glorious.Language.Kernel.StepObservation.of_loans (middle := _) rfl
      (Nat.le_of_eq nextRootEq.symm) (.of_eq regionState.1 regionState.2)
      (fun id loan found => StepFrame.row_of_before valid frame found)
      (fun id loan found =>
        let ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
        ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩)
      (fun authority access address reads permission => forward authority access address reads permission)
      claimChannel compatibleChannel
      (fun _ _ _ _ => Value.SupportFramed.of_roots rfl) framePermittedChannel

/-- The observation of a step that moves an erased storage-loan handle: the
unique handle changes only its custodian, and a shared view moves nothing. -/
theorem StepObservation.of_storageLoanTransfer {program : RuntimeProgram} {recipient : ClaimCustody}
    {region : Identity} {before after : World} {input : InvocationInput} {footprint : List Address}
    {other : InvocationInput} {identity : Identity} {type : Term}
    (valid : before.WellFormed) (frame : StepFrame before after)
    (formal : input.formal = .loan identity type) (_owned : input.access = .owned)
    (transferred : TransfersStorageLoan recipient before ⟨input.storage,input.authority⟩ after)
    (independent : input.IndependentOf program footprint before other)
    (_otherAccessible : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesAccessible program before other.access) :
    StepObservation program footprint region before after other := by
  have nextRootEq := TransfersStorageLoan.nextRoot transferred
  have regionState := Glorious.Language.TransfersStorageLoan.region_state transferred
  cases transferred with
  | unique authorityEq rowFound live kind mode referent =>
    rename_i movedIdentity movedLoan
    have loans : (custodyUpdate before movedIdentity {movedLoan with custody := some recipient}).loans =
        before.loans.set movedIdentity {movedLoan with custody := some recipient} := rfl
    have rootEq : (custodyUpdate before movedIdentity {movedLoan with custody := some recipient}).roots =
        before.roots := rfl
    have rowRelation := World.RowRelation.of_set
      (before := before)
      (after := custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
      rowFound loans (by simp only [Loan.permissionState])
    have locationsEq := Glorious.Language.World.LocationExtension.of_roots
      (before := before) (after := custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
      rootEq
    have rootPresent : ∀ address root, before.root address = some root →
        ∃ changed, (custodyUpdate before movedIdentity {movedLoan with custody := some recipient}).root
          address = some changed :=
      fun address root found =>
        ⟨root, by
          rw [Glorious.Language.World.root_of_roots
            (before := before)
            (after := custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
            rootEq address]
          exact found⟩
    have forward : ∀ authority access address, other.ReadsPermission before authority access address →
        Permitted before authority access address →
          Permitted (custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
            authority access address :=
      fun authority access address _ permission => Permitted.of_rows rowRelation rootPresent permission
    have claimChannel : ∀ authority address, other.ReadsClaim before authority address →
        AllocationClaim before authority address →
          AllocationClaim (custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
            authority address :=
      fun authority address _ held => AllocationClaim.of_rows rowRelation locationsEq held
    have compatibleChannel : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value →
          value.BatchCompatible before
            (custodyUpdate before movedIdentity {movedLoan with custody := some recipient}) :=
      fun localSlot value formal' stored =>
        Value.BatchCompatible.of_custody_update
          (before := before)
          (after := custodyUpdate before movedIdentity {movedLoan with custody := some recipient})
          (identity := movedIdentity) (original := movedLoan) (newCustody := recipient)
          (requested := movedLoan.returnRequested)
          locationsEq rowFound loans
          (Or.inr (Or.inr (fun resident authority access reached binding member =>
            independent.custody movedIdentity
              (Or.inr ⟨identity,type,formal,authorityEq,movedLoan,rowFound,mode⟩) binding.authority
              (Or.inr ⟨localSlot,value,formal',stored,
                ⟨resident,authority,access,reached,binding,member,rfl⟩⟩))))
    have framePermittedChannel : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value →
          value.FramePermitted before
            (custodyUpdate before movedIdentity {movedLoan with custody := some recipient}) other.access :=
      fun localSlot value formal' stored authority requested address views permission =>
        forward authority requested address (Or.inr ⟨localSlot,value,formal',stored,views⟩) permission
    exact Glorious.Language.Kernel.StepObservation.of_loans (middle := _) rfl
      (Nat.le_of_eq nextRootEq.symm) (.of_eq regionState.1 regionState.2)
      (fun id loan found => StepFrame.row_of_before valid frame found)
      (fun id loan found =>
        let ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
        ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩)
      (fun authority access address reads permission => forward authority access address reads permission)
      claimChannel compatibleChannel
      (fun _ _ _ _ => Value.SupportFramed.of_roots rfl) framePermittedChannel
  | shared _backingEq _parentEq _rowFound _live _kind _mode _referent =>
    exact Glorious.Language.Kernel.StepObservation.of_loans (middle := before) rfl
      (Nat.le_refl _) (.refl _)
      (fun _ _ found => ⟨_,found,rfl⟩)
      (fun _ _ found => ⟨_,found,rfl⟩)
      (fun authority access address _ permission => permission)
      (fun _ _ _ held => held)
      (fun _ _ _ _ =>
        Value.BatchCompatible.of_eq
          (Glorious.Language.World.LocationExtension.of_roots rfl) rfl)
      (fun _ _ _ _ => Value.SupportFramed.of_roots rfl)
      (fun _ _ _ _ _ _ _ _ permission => permission)


/-- A permission survives a step that retains the loan table, given a root at
the observed address. The same criterion is stated by the pattern-plan
transport, which is not in this module's import closure. -/
theorem Permitted.of_same_loans {before after : World} {address : Address}
    {authority : Authority} {access : Access}
    (loans : after.loans = before.loans) (root : ∃ root, after.root address = some root)
    (permitted : Permitted before authority access address) : Permitted after authority access address := by
  induction authority with
  | owner => exact ⟨root,by simpa only [loans] using permitted.2⟩
  | loan identity => exact ⟨root,permitted.2.transport loans⟩
  | shared backing ih => exact ⟨root,permitted.2.1,ih permitted.2.2⟩
  | guarded backing carrier ih =>
      obtain ⟨loan,selected,guard⟩ := permitted.2.2
      exact ⟨root,ih permitted.2.1,loan,by simpa only [loans] using selected,guard.transport loans⟩

/-- The world one value write produces. -/
abbrev writtenWorld (before : World) (address : Address) (root : Root) (replacement : Option Value) : World :=
  { before with roots := before.roots.set address.root { root with value := replacement } }

/-- The world one invocation lending step produces: the fresh handle value has
been written and one restoring row inserted at the loan frontier. -/
abbrev loanStepWorld (allocated handled : World) (storage : Address) (authority : Authority)
    (mode : Mutability) (sourceRegion : Identity) : World :=
  { handled with
    loans := allocated.loans.set allocated.nextLoan
      ⟨allocated.nextLoan,authority.parentLoan,storage,mode,sourceRegion,true,.restoring,
        authority.guardLoans allocated,false,none⟩
    nextOwner := allocated.nextOwner+1
    nextLoan := allocated.nextLoan+1 }

theorem LendsResident.old_roots {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {address : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease}
    (lent : LendsResident program activation scope region before address authority access lease result after)
    {identity : Identity} (bound : identity < before.nextRoot) :
    after.roots.get identity = before.roots.get identity := by
  cases lent with
  | owned => rfl
  | lent _ _ _ allocated formed =>
    cases formed with
    | borrow _ _ _ _ _ _ _ _ _ _ written =>
      rw [StepFrame.write_roots_other written (by rw [(Allocates.fresh_root allocated).1]; exact Nat.ne_of_lt bound)]
      cases allocated
      exact Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)

theorem LendsResident.locationExtension {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {address : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease result after) :
    before.LocationExtension after := by
  cases lent with
  | owned => exact .of_locations (fun _ => rfl)
  | lent _ _ _ allocated formed =>
    exact (allocated.locationExtension valid).trans (.of_locations formed.locations)

/-- The same actual fresh-root and restoring-row producer frames reachable
values belonging to inputs, whole receivers, and contextual witnesses. -/
theorem LendsResident.batchFrame {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {address : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} {value : Value} {incoming : Access} (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease result after)
    (permission : Permitted before authority access address)
    (ready : value.ResourcesAccessible program before incoming) :
    value.BatchCompatible before after ∧ value.SupportFramed before after := by
  have locations := lent.locationExtension valid
  have framed : value.SupportFramed before after := by
    intro observed supported
    have roots := lent.old_roots (Value.Support.root_bound valid ready supported)
    refine ⟨?_,congrArg (Option.map Root.location) roots⟩
    unfold World.read World.root
    rw [roots]
  refine ⟨?_,framed⟩
  cases lent with
  | owned => exact ⟨fun _ _ _ _ => rfl,fun _ _ _ _ _ _ held => held⟩
  | lent modes stored borrowRegion allocated formed =>
    rename_i mode original handle allocatedWorld layout sourceRegion
    cases formed with
    | borrow _ _ _ _ _ _ _ _ _ parentEq written =>
      cases parentEq
      have rows := Allocates.loans allocated
      have guards := Authority.guardLoans.loans_congr rows authority
      refine Value.BatchCompatible.of_fresh_loan (fresh :=
        ⟨before.nextLoan,authority.parentLoan,address,mode,sourceRegion,true,.restoring,
          authority.guardLoans before,false,none⟩) valid locations ?_ ready.2.1 ?_ ?_
      · change _ = before.loans.set before.nextLoan _
        rw [rows,Allocates.nextLoan allocated,guards]
        rfl
      · exact fun identity selected => Permitted.parentLoan_bound valid permission identity selected
      · exact fun _ _ _ _ _ _ => Or.inl (fun same => by cases same)

/-- Old access survives lending exactly when it is compatible with the real
new row. The condition is read only in the original world. -/
theorem LendsResident.permitted {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {source observed : Address} {authority result query : Authority}
    {access requested : Access} {lease : Option InvocationLease} (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before source authority access lease result after)
    (permission : Permitted before query requested observed)
    (compatible : access ≠ .owned → query.LoanCompatible before requested observed source
      (if access = .shared then .shared else .unique) (authority.guardLoans before)) :
    Permitted after query requested observed := by
  cases lent with
  | owned => exact permission
  | lent modes stored borrowRegion allocated formed =>
    rename_i mode value handle allocatedWorld layout sourceRegion
    have borrowed : access ≠ .owned := by rcases modes with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp
    have modeEq : mode = if access = .shared then Mutability.shared else .unique := by
      rcases modes with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
    apply formed.permitted (allocated.wellFormed valid)
      (permission.locationExtension (allocated.locationExtension valid) allocated.loans)
    rw [Authority.guardLoans.loans_congr allocated.loans authority,modeEq]
    exact Authority.LoanCompatible.loans_congr allocated.loans (compatible borrowed)

theorem LendsResident.resourcesAccessible {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {source : Address} {authority result : Authority}
    {access incoming : Access} {lease : Option InvocationLease} {value : Value} (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before source authority access lease result after)
    (permission : Permitted before authority access source)
    (ready : value.ResourcesAccessible program before incoming)
    (compatible : access ≠ .owned → value.ViewsLoanCompatible before incoming source
      (if access = .shared then .shared else .unique) (authority.guardLoans before)) :
    value.ResourcesAccessible program after incoming := by
  obtain ⟨batch,framed⟩ := lent.batchFrame valid permission ready
  exact ready.frame_input batch framed (fun query requested observed views held =>
    lent.permitted valid held (fun borrowed => compatible borrowed query requested observed views))


theorem LendsResident.addressType {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {source observed : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} {type : Term} (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before source authority access lease result after)
    (typed : AddressType program.declarations before observed type) :
    AddressType program.declarations after observed type := by
  obtain ⟨root,found⟩ := typed.root_exists
  have bound := World.root_bound valid (World.root_found found).1
  cases lent with
  | owned => exact typed
  | lent _ _ _ allocated formed =>
    cases formed with
    | borrow stored referentType initialized live admitted resources permission vacant destinationType parentEq written =>
      rename_i original writtenWorld parent
      have retained := (World.write_address_types written
        (Address.not_properPrefix_of_root_ne (by rw [(Allocates.fresh_root allocated).1]; exact (Nat.ne_of_lt bound).symm))).mp
          (allocated.addressType valid typed)
      refine AddressType.roots_congr (before := writtenWorld) ?_ retained
      rfl

/-- A prior physical request crosses a receiver loan by its unchanged region
state, actual address-layout derivation, and retained region-bearing rows. -/
theorem LendsResident.Request.frame {program : RuntimeProgram} {activation scope region targetRegion : Identity}
    {before after : World} {source observed : Address} {authority result query : Authority}
    {access requested : Access} {lease : Option InvocationLease} {type : Term} (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before source authority access lease result after)
    (request : LendsResident.Request program before targetRegion observed query requested type) :
    LendsResident.Request program after targetRegion observed query requested type := by
  intro borrowed
  obtain ⟨loanRegion,layout,borrowRegion,typed,request⟩ := request borrowed
  exact ⟨loanRegion,layout,borrowRegion.transport (lent.locationExtension valid)
    (fun _ loan found => ⟨loan,lent.loan_retained valid found,rfl⟩),lent.addressType valid typed,
    request.same_regions lent.region_state.1 lent.region_state.2⟩

theorem Authority.LoanCompatible.no_conflict {world : World} {authority : Authority}
    {requested : Access} {address referent : Address} {mode : Mutability} {guards : List Identity}
    (compatible : authority.LoanCompatible world requested address referent mode guards) :
    address.Overlaps referent → ¬ Conflict requested mode := by
  induction authority with
  | owner => exact compatible
  | loan _ => exact compatible.1
  | shared _ ih => exact ih compatible
  | guarded _ _ ih => exact ih compatible.1

/-- The newly minted borrower observes the same overlap condition. It cannot
be an inherited guard of a second original authority: those identities were
already below the original loan frontier. -/
theorem LendsResident.borrowerCompatible {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {source address observed : Address} {authority result : Authority} {access requested : Access}
    {lease : Option InvocationLease} {mode : Mutability} {guards : List Identity}
    (lent : LendsResident program activation scope region before source authority access lease result after)
    (compatible : authority.LoanCompatible before requested address observed mode guards)
    (bounds : ∀ identity ∈ guards, identity < before.nextLoan) :
    result.LoanCompatible after requested address observed mode guards := by
  cases lent with
  | owned => exact compatible
  | lent _ _ _ allocated _ =>
    refine ⟨Authority.LoanCompatible.no_conflict compatible,?_⟩
    intro member
    rw [Allocates.nextLoan allocated] at member
    exact False.elim (Nat.lt_irrefl _ (bounds _ member))


/-- One actual receiver-lending observation: owned access leaves the world
unchanged; shared/unique access creates a fresh handle and restoring row.
Ordinary input binders supply the same observed-permission condition. -/
theorem StepObservation.of_lendsResident {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {inputStorage : Address} {inputAuthority : Authority} {inputAccess : Access}
    {footprint : List Address} {other : InvocationInput} {lease : Option InvocationLease} {authority : Authority}
    (valid : before.WellFormed)
    (permission : Permitted before inputAuthority inputAccess inputStorage)
    (lent : LendsResident program activation scope region before inputStorage inputAuthority inputAccess lease authority after)
    (compatible : inputAccess ≠ .owned → ∀ query requested address, other.ReadsPermission before query requested address →
      query.LoanCompatible before requested address inputStorage
        (if inputAccess = .shared then .shared else .unique) (inputAuthority.guardLoans before))
    (otherReady : other.ReadyFor program before footprint) (otherBound : other.storage.root < before.nextRoot) :
    StepObservation program footprint region before after other := by
    cases lent with
    | owned =>
      exact ⟨fun _ _ stored => stored,fun _ _ stored => stored,Nat.le_refl _,fun located => located,fun _ typed => typed,
        fun _ _ permission => permission,fun claim => claim,
        fun _ loan found => ⟨loan,found,rfl⟩,fun _ loan found => ⟨loan,found,rfl⟩,fun _ _ region => region,.refl _,
        fun _ _ _ _ => ⟨⟨fun _ _ _ _ => rfl,fun _ _ _ _ _ _ held => held⟩,
          fun _ _ => ⟨rfl,rfl⟩⟩,fun _ _ _ _ _ _ _ _ held => held⟩
    | lent modes sourceStored borrowRegion allocProof formed =>
      rename_i lentMode lentValue lentHandle lentAllocated lentLayout lentRegion
      have borrowed : inputAccess ≠ .owned := by rcases modes with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp
      cases formed with
      | borrow fsValue fsType fsInitialized fsLive fsAdmitted fsAccessible fsPermitted fsVacant
          fsDestType parentEq written =>
        rename_i borrowedValue borrowedResult borrowedParent
        cases parentEq
        obtain ⟨writtenRoot,writtenValue,writtenFound,rfl⟩ := World.write_value_update written
        change StepObservation program footprint region before
          (loanStepWorld lentAllocated (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
            inputStorage inputAuthority lentMode lentRegion) other
        have handleRoot : lentHandle.root = before.nextRoot := (Allocates.fresh_root allocProof).1
        have allocatedValid : lentAllocated.WellFormed := Allocates.wellFormed valid allocProof
        have allocatedLoans : lentAllocated.loans = before.loans := Allocates.loans allocProof
        have guardsEq : inputAuthority.guardLoans lentAllocated = inputAuthority.guardLoans before :=
          Authority.guardLoans.loans_congr allocatedLoans inputAuthority
        have apart : other.storage.root ≠ lentHandle.root := by
          rw [handleRoot]
          exact Nat.ne_of_lt otherBound
        have handleRootNe : lentHandle.root ≠ other.storage.root := apart.symm
        have formed' : FormsLoan program .invocation lentAllocated inputAuthority lentMode lentRegion
            inputStorage lentHandle
            (loanStepWorld lentAllocated (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              inputStorage inputAuthority lentMode lentRegion) :=
          .borrow fsValue fsType fsInitialized fsLive fsAdmitted fsAccessible fsPermitted fsVacant
            fsDestType rfl written
        have readWhole : (loanStepWorld lentAllocated
            (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
            inputStorage inputAuthority lentMode lentRegion).read other.storage = before.read other.storage :=
          (World.read_of_roots (before := writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
            (after := loanStepWorld lentAllocated (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              inputStorage inputAuthority lentMode lentRegion) rfl other.storage).trans
            ((World.read_root_other (before := lentAllocated)
              (after := writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              (mutation := lentHandle) written apart).trans (Allocates.read valid allocProof other.storage))
        have loansWhole : (loanStepWorld lentAllocated
            (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
            inputStorage inputAuthority lentMode lentRegion).loans =
            before.loans.set before.nextLoan
              ⟨before.nextLoan,inputAuthority.parentLoan,inputStorage,lentMode,lentRegion,true,
                .restoring,inputAuthority.guardLoans before,false,none⟩ := by
          change lentAllocated.loans.set lentAllocated.nextLoan
              ⟨lentAllocated.nextLoan,inputAuthority.parentLoan,inputStorage,lentMode,lentRegion,true,
                .restoring,inputAuthority.guardLoans lentAllocated,false,none⟩ =
            before.loans.set before.nextLoan
              ⟨before.nextLoan,inputAuthority.parentLoan,inputStorage,lentMode,lentRegion,true,
                .restoring,inputAuthority.guardLoans before,false,none⟩
          rw [allocatedLoans, Allocates.nextLoan allocProof, guardsEq]
        have stepLocations : lentAllocated.LocationExtension
            (loanStepWorld lentAllocated (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              inputStorage inputAuthority lentMode lentRegion) :=
          World.LocationExtension.of_locations (before := lentAllocated)
            (after := loanStepWorld lentAllocated
              (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              inputStorage inputAuthority lentMode lentRegion)
            (fun id => by
              change Option.map Root.location
                  ((writtenWorld lentAllocated lentHandle writtenRoot writtenValue).roots.get id) =
                Option.map Root.location (lentAllocated.roots.get id)
              exact World.write_locations written id)
        have stepLoans : (loanStepWorld lentAllocated
            (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
            inputStorage inputAuthority lentMode lentRegion).loans =
            lentAllocated.loans.set lentAllocated.nextLoan
              ⟨lentAllocated.nextLoan,inputAuthority.parentLoan,inputStorage,lentMode,lentRegion,true,
                .restoring,inputAuthority.guardLoans lentAllocated,false,none⟩ := rfl
        have locationsWhole : before.LocationExtension
            (loanStepWorld lentAllocated (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              inputStorage inputAuthority lentMode lentRegion) :=
          (Allocates.locationExtension valid allocProof).trans stepLocations
        have modeEq : lentMode = if inputAccess = .shared then .shared else .unique := by
          rcases modes with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
        have parentBound : ∀ p,
            (⟨before.nextLoan,inputAuthority.parentLoan,inputStorage,lentMode,lentRegion,true,
              .restoring,inputAuthority.guardLoans before,false,none⟩ : Loan).parent = some p →
            p < before.nextLoan :=
          fun p same => Permitted.parentLoan_bound valid permission p same
        have afterPermitted : ∀ (authority' : Authority) (access : Access) (address : Address),
            Permitted before authority' access address → Permitted lentAllocated authority' access address :=
          fun authority' access address held => by
            obtain ⟨root,rootFound⟩ := held.root
            exact Permitted.of_same_loans allocatedLoans
              ⟨root,Allocates.root valid allocProof rootFound⟩ held
        have formedPermitted : ∀ (authority' : Authority) (access : Access) (address : Address),
            other.ReadsPermission before authority' access address →
            Permitted lentAllocated authority' access address →
              Permitted (loanStepWorld lentAllocated
                (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
                inputStorage inputAuthority lentMode lentRegion) authority' access address :=
          fun authority' access address reads held =>
            (FormsLoan.permitted_iff allocatedValid formed' held).mpr
              (guardsEq.symm ▸ Authority.LoanCompatible.loans_congr allocatedLoans
                (by simpa only [modeEq] using compatible borrowed authority' access address reads))
        refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · intro _ value' stored'
          rw [World.Stores] at stored' ⊢
          rw [readWhole]
          exact stored'
        · intro _ value' stored'
          rw [World.Stores] at stored' ⊢
          rw [← readWhole]
          exact stored'
        · change before.nextRoot ≤ lentAllocated.nextRoot
          rw [(Allocates.fresh_root allocProof).2]
          exact Nat.le_succ _
        · intro located
          exact World.Located.of_roots (before := writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
            (after := loanStepWorld lentAllocated
              (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              inputStorage inputAuthority lentMode lentRegion) rfl
            (World.write_located written (Address.not_properPrefix_of_root_ne handleRootNe)
              (Allocates.located valid allocProof located))
        · intro term located
          exact AddressType.roots_congr
            (before := writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
            (after := loanStepWorld lentAllocated
              (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              inputStorage inputAuthority lentMode lentRegion) rfl
            ((World.write_address_types (program := program.declarations) written
              (Address.not_properPrefix_of_root_ne handleRootNe)).mp
              (Allocates.addressType valid allocProof located))
        · intro requested observed permitted'
          exact formedPermitted other.authority requested other.storage
            (Or.inl ⟨rfl,rfl,observed,permitted'⟩)
            (afterPermitted other.authority requested other.storage permitted')
        · intro held
          obtain ⟨anchor,claimLoan,claimRoot,claimDomain,atAnchor,claimFound,claimLive,claimKind,
            claimReferent,claimWhole,claimSelected,claimHome,claimLatest⟩ := held
          exact AllocationClaim.fresh_loan_nonowning (before := before)
            (after := loanStepWorld lentAllocated
              (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              inputStorage inputAuthority lentMode lentRegion) valid locationsWhole loansWhole
            ⟨anchor,claimLoan,claimRoot,claimDomain,atAnchor,claimFound,claimLive,claimKind,
              claimReferent,claimWhole,claimSelected,claimHome,claimLatest⟩
            atAnchor parentBound (fun same => by cases same)
        · intro id loan found
          exact ⟨loan,World.fresh_loan_retained valid loansWhole found,rfl⟩
        · intro id loan found
          exact ⟨loan,World.fresh_loan_retained valid loansWhole found,rfl⟩
        · intro address regionId borrowed'
          exact Authority.BorrowRegion.transport stepLocations
            (World.fresh_loan_region (before := lentAllocated) (after := loanStepWorld lentAllocated
              (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              inputStorage inputAuthority lentMode lentRegion) allocatedValid stepLoans)
            (Authority.BorrowRegion.allocates valid allocProof borrowed')
        · refine World.RegionExtension.of_eq ?_ ?_
          · exact (FormsLoan.region_state formed').1.trans (Allocates.region_state allocProof).1
          · exact (FormsLoan.region_state formed').2.trans (Allocates.region_state allocProof).2
        · intro localSlot value' formal' stored'
          exact (LendsResident.lent modes sourceStored borrowRegion allocProof formed').batchFrame valid permission
            (InvocationInput.ReadyFor.resident otherReady (by rw [formal']; trivial) stored').2.2.1.1
        · intro localSlot value' formal' stored' authority' requested address views permitted'
          exact formedPermitted authority' requested address
            (Or.inr ⟨localSlot,value',formal',stored',views⟩)
            (afterPermitted authority' requested address permitted')


/-- The observation of one actual owned-resident handoff: a fresh root receives
the moved value and the source storage is clearedEq. -/
theorem StepObservation.of_ownedTransfer {program : RuntimeProgram} {activation scope region : Identity}
    {before after allocated : World} {input : InvocationInput} {footprint : List Address}
    {other : InvocationInput} {layout : Layout} {address : Address}
    (valid : before.WellFormed) (frame : StepFrame before after)
    (owned : input.access = .owned) (residentFormal : input.formal.IsResident)
    (allocation : Allocates program.declarations before (.localSlot activation scope) region
      input.formal.type layout input.formal.mutable address allocated)
    (transferred : Transfers program allocated input.authority input.storage address after)
    (independent : input.IndependentOf program footprint before other)
    (otherReady : other.ReadyFor program before footprint)
    (otherBound : other.storage.root < before.nextRoot)
    (licensed : ∀ observed ∈ input.clearedStorage, observed ∈ footprint)
    (_otherAccessible : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesAccessible program before other.access) :
    StepObservation program footprint region before after other := by
  cases transferred with
  | move _sourceStored _movedInitialized _moveReady _permittedAllocated _vacant _separated
      _destinationType clearedEq installEq =>
    rename_i movedValue clearedWorld
    have allocatedValid : allocated.WellFormed := Allocates.wellFormed valid allocation
    have allocatedLoans : allocated.loans = before.loans := Allocates.loans allocation
    have destinationRoot : address.root = before.nextRoot := (Allocates.fresh_root allocation).1
    have destinationNe : address.root ≠ other.storage.root := by
      rw [destinationRoot]
      exact (Nat.ne_of_lt otherBound).symm
    obtain ⟨localSlot,formalEq⟩ := Kernel.InputFormal.exists_resident_of_isResident residentFormal
    have sourceMember : input.storage ∈ input.clearedStorage := by
      simp only [InvocationInput.clearedStorage,formalEq,owned,if_true]
      exact List.mem_singleton_self _
    have sourceApart : ¬ input.storage.Overlaps other.storage :=
      independent.clear input.storage sourceMember
    have sourceNotPrefix : ¬ input.storage.ProperPrefix other.storage :=
      Address.not_properPrefix_of_not_overlaps sourceApart
    have destinationApart : ¬ address.Overlaps other.storage :=
      World.not_overlaps_of_root_ne destinationNe
    have destinationNotPrefix : ¬ address.ProperPrefix other.storage :=
      Address.not_properPrefix_of_root_ne destinationNe
    have writeLocations : ∀ id, (after.roots.get id).map Root.location =
        (allocated.roots.get id).map Root.location :=
      fun id => (World.write_locations installEq id).trans (World.write_locations clearedEq id)
    have stepLoans : after.loans = allocated.loans :=
      (World.write_loans installEq).trans (World.write_loans clearedEq)
    have locationsWhole : before.LocationExtension after :=
      (Allocates.locationExtension valid allocation).trans
        (World.LocationExtension.of_locations writeLocations)
    have loansWhole : after.loans = before.loans := stepLoans.trans allocatedLoans
    have installRoot : after.nextRoot = clearedWorld.nextRoot := by
      obtain ⟨_,_,_,rfl⟩ := World.write_value_update installEq
      rfl
    have clearedRoot : clearedWorld.nextRoot = allocated.nextRoot := by
      obtain ⟨_,_,_,rfl⟩ := World.write_value_update clearedEq
      rfl
    have rootPresent : ∀ observed root, allocated.root observed = some root →
        ∃ changed, after.root observed = some changed :=
      fun observed root found => by
        obtain ⟨changed,selected,_⟩ := World.root_transport writeLocations found
        exact ⟨changed,selected⟩
    have afterPermitted : ∀ (authority' : Authority) (access : Access) (observed : Address),
        Permitted before authority' access observed → Permitted allocated authority' access observed :=
      fun authority' access observed held => by
        obtain ⟨root,rootFound⟩ := held.root
        exact Permitted.of_same_loans allocatedLoans
          ⟨root,Allocates.root valid allocation rootFound⟩ held
    have movedPermitted : ∀ (authority' : Authority) (access : Access) (observed : Address),
        Permitted allocated authority' access observed → Permitted after authority' access observed :=
      fun authority' access observed held =>
        Permitted.of_rows (before := allocated) (after := after)
          (World.RowRelation.of_eq stepLoans) rootPresent held
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro _ value' stored'
      exact (World.Stores.write_disjoint_iff installEq destinationApart).mp
        ((World.Stores.write_disjoint_iff clearedEq sourceApart).mp
          ((Allocates.stores_iff valid allocation).mp stored'))
    · intro _ value' stored'
      exact (Allocates.stores_iff valid allocation).mpr
        ((World.Stores.write_disjoint_iff clearedEq sourceApart).mpr
          ((World.Stores.write_disjoint_iff installEq destinationApart).mpr stored'))
    · rw [installRoot, clearedRoot, (Allocates.fresh_root allocation).2]
      exact Nat.le_succ _
    · intro located
      exact World.write_located installEq destinationNotPrefix
        (World.Located.write_disjoint clearedEq sourceApart
          (Allocates.located valid allocation located))
    · intro term located
      exact (World.write_address_types (program := program.declarations) installEq destinationNotPrefix).mp
        ((World.write_address_types (program := program.declarations) clearedEq sourceNotPrefix).mp
          (Allocates.addressType valid allocation located))
    · intro requested _ permitted'
      exact movedPermitted other.authority requested other.storage
        (afterPermitted other.authority requested other.storage permitted')
    · intro held
      have allocatedHeld : AllocationClaim allocated other.authority other.storage :=
        AllocationClaim.of_rows (World.RowRelation.of_eq allocatedLoans)
          (Allocates.locationExtension valid allocation) held
      exact AllocationClaim.of_rows (before := allocated) (after := after)
        (World.RowRelation.of_eq stepLoans)
        (World.LocationExtension.of_locations writeLocations) allocatedHeld
    · intro id loan found
      exact StepFrame.row_of_before valid frame found
    · intro id loan found
      let ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
      exact ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩
    · intro observed regionId borrowed'
      exact Authority.BorrowRegion.transport
        (World.LocationExtension.of_locations writeLocations)
        (fun id loan found => ⟨loan,by rw [stepLoans]; exact found,rfl⟩)
        (Authority.BorrowRegion.allocates (before := before) (after := allocated)
          valid allocation borrowed')
    · refine World.RegionExtension.of_eq ?_ ?_
      · exact (World.write_region_state installEq).1.trans
          ((World.write_region_state clearedEq).1.trans (Allocates.region_state allocation).1)
      · exact (World.write_region_state installEq).2.trans
          ((World.write_region_state clearedEq).2.trans (Allocates.region_state allocation).2)
    · intro localSlot value' formal' stored'
      have handoffBefore : value'.HandoffReady program before other.access footprint :=
        (InvocationInput.ReadyFor.resident otherReady (by rw [formal']; trivial) stored').2.2.1
      have handoffAllocated : value'.HandoffReady program allocated other.access footprint :=
        Allocates.handoffReady valid allocation handoffBefore
      have framedAllocated : value'.SupportFramed before allocated :=
        Allocates.supportFramed valid allocation handoffBefore.1
      have framedAfter : value'.SupportFramed allocated after :=
        Value.SupportFramed.of_two_writes clearedEq installEq (World.write_loans clearedEq)
          (fun observed supported =>
            (handoffAllocated.2 input.storage (licensed input.storage sourceMember)) observed supported)
          (fun observed supported =>
            World.not_overlaps_of_root_ne (by
              rw [destinationRoot]
              exact (Nat.ne_of_lt (Value.Support.root_bound valid handoffBefore.1
                ((Value.Support.frame allocatedLoans framedAllocated).mpr supported))).symm))
      exact ⟨Value.BatchCompatible.of_eq locationsWhole loansWhole,
        framedAllocated.trans allocatedLoans framedAfter⟩
    · intro localSlot value' formal' stored' authority' requested observed views permitted'
      exact movedPermitted authority' requested observed
        (afterPermitted authority' requested observed permitted')


/-- Every actual binding rule is observed by every still-pending input: the six
per-rule producers composed under one dispatcher. -/
theorem BindsInputAt.stepObservation {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before middle : World} {input : InvocationInput}
    {binding : Binding} {footprint : List Address} {other : InvocationInput}
    (valid : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding middle)
    (independent : input.IndependentOf program footprint before other)
    (otherReady : other.ReadyFor program before footprint)
    (_otherRecorded : other.authority.Recorded before.loans)
    (otherBound : other.storage.root < before.nextRoot)
    (licensed : ∀ address ∈ input.clearedStorage, address ∈ footprint)
    (otherAccessible : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesAccessible program before other.access) :
    StepObservation program footprint region before middle other := by
  have frame : StepFrame before middle := BindsInputAt.stepFrame valid bound
  cases bound with
  | lent ready borrowed resident stored initialized type permission lent =>
      have fresh : input.FreshRow before input.storage (if input.access = .shared then .shared else .unique)
          (input.authority.guardLoans before) .restoring := by
        obtain ⟨localSlot,formal⟩ := Kernel.InputFormal.exists_resident_of_isResident resident
        rw [InvocationInput.FreshRow,formal]
        exact ⟨borrowed,rfl,rfl,rfl,rfl⟩
      exact StepObservation.of_lendsResident valid permission lent
        (fun _ => independent.permission _ _ _ _ fresh) otherReady otherBound
  | owned ready owning resident stored type allocated transferred =>
      exact StepObservation.of_ownedTransfer valid frame owning resident allocated transferred
        independent otherReady otherBound licensed otherAccessible
  | storage ready formal locatedType claimed =>
      exact StepObservation.of_storageClaim valid frame formal claimed independent
        otherAccessible
  | allocation ready formal owning locatedType transferred =>
      exact StepObservation.of_allocationTransfer valid frame formal owning transferred independent
        otherAccessible
  | guardedAllocation ready formal owning guarded locatedType claimed =>
      exact StepObservation.of_guardedClaim valid frame formal owning ⟨_,_,guarded⟩ claimed independent
        otherAccessible
  | loan ready formal owning locatedType transferred =>
      exact StepObservation.of_storageLoanTransfer valid frame formal owning transferred independent
        otherAccessible


/-- The facts one already-emitted binding keeps as the batch advances: its key,
its storage typing (for a resident port) and the live resource row that carries
its authority to the emitted address. -/
structure OutputFramed (program : RuntimeProgram) (world : World) (input : InvocationInput)
    (binding : Binding) : Prop where
  key : binding.key = input.formal.key
  typed : input.formal.IsResident →
    Typing.BindingStorageTyped program.declarations world binding.address input.formal.type
  row : ∀ identity, binding.authority.parentLoan = some identity →
    ∃ loan, world.loans.get identity = some loan ∧ loan.live = true ∧ loan.referent = binding.address

/-- Every emitted binding survives every later binding of the same batch: the
key is its own, the storage typing is retained by the actual rule, and the
authority row keeps its live permission projection. -/
theorem OutputFramed.frame {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before middle : World} {input : InvocationInput}
    {stepBinding : Binding} {output : InvocationInput} {outputBinding : Binding}
    (valid : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input stepBinding middle)
    (facts : OutputFramed program before output outputBinding) :
    OutputFramed program middle output outputBinding := by
  refine ⟨facts.key,?_,?_⟩
  · intro resident
    exact BindsInputAt.preserves_bindingStorageType valid bound (facts.typed resident)
  · intro identity atIdentity
    obtain ⟨loan,found,live,referent⟩ := facts.row identity atIdentity
    obtain ⟨current,selected,shape⟩ := BindsInputAt.loan_retained valid bound found
    obtain ⟨_,_,referentEq,_,_,liveEq,_,_⟩ := Loan.permissionState_eq_iff.mp shape
    exact ⟨current,selected,liveEq.trans live,referentEq.trans referent⟩




/-- The binding emitted by one storage claim is framed: its key names the port
and the fresh storage-borrow row carries its authority to the emitted address. -/
theorem OutputFramed.of_storageClaim {program : RuntimeProgram} {recipient : ClaimCustody}
    {before after : World} {input : InvocationInput} {identity : Identity} {type : Term}
    {created : Identity}
    (_valid : before.WellFormed) (formal : input.formal = .storage identity type)
    (claimed : ClaimsStorage recipient before input.authority input.access input.storage created after) :
    OutputFramed program after input
      ⟨.resourceInput identity,input.storage,ClaimedAuthority input.access created⟩ := by
  obtain ⟨rowRoot,rowFound⟩ := ClaimsStorage.fresh_row claimed
  refine ⟨by rw [formal]; simp only [InputFormal.key],?_,?_⟩
  · intro residentFormal
    exact absurd residentFormal (by intro h; simp only [InputFormal.IsResident,formal] at h)
  · intro identity' same
    cases claimed with
    | claim rowLocated rowPermitted =>
      have identityEq : identity' = before.nextLoan := by
        by_cases shared : input.access = .shared
        · have held : (Authority.shared (.loan before.nextLoan)).parentLoan = some identity' := by
            simpa only [ClaimedAuthority,if_pos shared] using same
          exact (Option.some.inj (by simpa only [Authority.parentLoan] using held)).symm
        · have held : (Authority.loan before.nextLoan).parentLoan = some identity' := by
            simpa only [ClaimedAuthority,if_neg shared] using same
          exact (Option.some.inj (by simpa only [Authority.parentLoan] using held)).symm
      subst identityEq
      exact ⟨_,rowFound,rfl,rfl⟩

/-- The binding emitted by one guarded allocation claim is framed. -/
theorem OutputFramed.of_guardedClaim {program : RuntimeProgram} {recipient : ClaimCustody}
    {before after : World} {input : InvocationInput} {identity : Identity} {type : Term}
    {created : Identity}
    (_valid : before.WellFormed) (formal : input.formal = .allocation identity type)
    (_owned : input.access = .owned)
    (claimed : ClaimsAllocation recipient before input.authority input.storage created after) :
    OutputFramed program after input ⟨.resourceInput identity,input.storage,.loan created⟩ := by
  obtain ⟨rowRoot,rowFound⟩ := ClaimsAllocation.fresh_row claimed
  refine ⟨by rw [formal]; simp only [InputFormal.key],?_,?_⟩
  · intro residentFormal
    exact absurd residentFormal (by intro h; simp only [InputFormal.IsResident,formal] at h)
  · intro identity' same
    cases claimed with
    | claim _ _ _ =>
      have identityEq : identity' = before.nextLoan :=
        (Option.some.inj (by simpa only [Authority.parentLoan] using same)).symm
      subst identityEq
      exact ⟨_,rowFound,rfl,rfl⟩

/-- The binding emitted by one whole-allocation custody handoff is framed. -/
theorem OutputFramed.of_allocationTransfer {program : RuntimeProgram} {recipient : ClaimCustody}
    {before after : World} {input : InvocationInput} {identity : Identity} {type : Term}
    (_valid : before.WellFormed) (formal : input.formal = .allocation identity type)
    (_owned : input.access = .owned) (ready : input.ReadyFor program before input.clearedStorage)
    (transferred : TransfersAllocation recipient before ⟨input.storage,input.authority⟩ after) :
    OutputFramed program after input ⟨.resourceInput identity,input.storage,input.authority⟩ := by
  cases input with
  | mk origin inputFormal inputStorage inputAuthority inputAccess =>
    have formalEq : inputFormal = .allocation identity type := by simpa using formal
    have ownedEq : inputAccess = .owned := by simpa using _owned
    simp only [InvocationInput.ReadyFor,formalEq] at ready
    obtain ⟨ownedAt,locatedType,claim,authorityForm⟩ := ready
    obtain ⟨anchor,claimLoan,claimRoot,claimDomain,atAnchor,claimFound,claimLive,claimKind,
      claimReferent,claimWhole,claimSelected,claimHome,claimLatest⟩ := claim
    refine ⟨by rw [formalEq]; simp only [InputFormal.key],?_,?_⟩
    · intro residentFormal
      exact absurd residentFormal (by intro h; simp only [InputFormal.IsResident,formalEq] at h)
    · intro identity' same
      have same' : inputAuthority.parentLoan = some identity' := by simpa using same
      have movedEq : identity' = anchor :=
        (Option.some.inj (by simpa only [Authority.parentLoan] using atAnchor.symm.trans same')).symm
      subst movedEq
      obtain ⟨current,selected,shape⟩ := TransfersAllocation.retained transferred claimFound
      obtain ⟨_,_,referentEq,_,_,liveEq,_,_⟩ := Loan.permissionState_eq_iff.mp shape
      exact ⟨current,selected,liveEq.trans claimLive,by rw [referentEq]; exact claimReferent⟩


/-- The binding emitted by one erased storage-loan handoff is framed: the row
the port was ready with stays live at the emitted address. -/
theorem OutputFramed.of_storageLoanTransfer {program : RuntimeProgram} {recipient : ClaimCustody}
    {before after : World} {input : InvocationInput} {identity : Identity} {type : Term}
    (_valid : before.WellFormed) (formal : input.formal = .loan identity type)
    (_owned : input.access = .owned) (ready : input.ReadyFor program before input.clearedStorage)
    (transferred : TransfersStorageLoan recipient before ⟨input.storage,input.authority⟩ after) :
    OutputFramed program after input ⟨.resourceInput identity,input.storage,input.authority⟩ := by
  cases input with
  | mk origin inputFormal inputStorage inputAuthority inputAccess =>
    have formalEq : inputFormal = .loan identity type := by simpa using formal
    have ownedEq : inputAccess = .owned := by simpa using _owned
    simp only [InvocationInput.ReadyFor,formalEq,ownedEq] at ready
    obtain ⟨ownedAt,locatedType,rowIdentity,row,rowFound,rowLive,rowKind,rowReferent,
      authorityForm⟩ := ready
    refine ⟨by rw [formalEq]; simp only [InputFormal.key],?_,?_⟩
    · intro residentFormal
      exact absurd residentFormal (by intro h; simp only [InputFormal.IsResident,formalEq] at h)
    · intro identity' same
      have same' : inputAuthority.parentLoan = some identity' := by simpa using same
      have identityEq : identity' = rowIdentity := by
        rcases authorityForm with ⟨loanAt,uniqueMode⟩ | ⟨backing,shared,parent,sharedMode⟩
        · exact (Option.some.inj (by simpa only [Authority.parentLoan] using
            (congrArg Authority.parentLoan loanAt).symm.trans same')).symm
        · simp only [shared,Authority.parentLoan] at same'
          rw [parent] at same'
          exact (Option.some.inj same').symm
      subst identityEq
      obtain ⟨current,selected,shape⟩ := TransfersStorageLoan.retained transferred rowFound
      obtain ⟨_,_,referentEq,_,_,liveEq,_,_⟩ := Loan.permissionState_eq_iff.mp shape
      exact ⟨current,selected,liveEq.trans rowLive,by rw [referentEq]; exact rowReferent⟩

/-- The binding emitted by one invocation lending step is framed. -/
theorem OutputFramed.of_lendsResident {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {input : InvocationInput} {lease : Option InvocationLease}
    {authority : Authority}
    (valid : before.WellFormed) (borrowed : input.access ≠ .owned)
    (type : ∀ (v : Value), before.Stores input.storage v → v.type = input.formal.type)
    (lent : LendsResident program activation scope region before input.storage input.authority input.access
      lease authority after) :
    OutputFramed program after input ⟨input.formal.key,input.storage,authority⟩ := by
  cases input with
  | mk origin inputFormal inputStorage inputAuthority inputAccess =>
    cases lent with
    | owned => exact absurd rfl borrowed
    | lent modes sourceStored borrowRegion allocated formed =>
      rename_i lentMode lentValue lentHandle lentAllocated lentLayout lentRegion
      have typeEq : lentValue.type = inputFormal.type := type lentValue sourceStored
      have rowFound := FormsLoan.fresh_row formed
      refine ⟨rfl,?_,?_⟩
      · intro _
        have storedAllocated : lentAllocated.Stores inputStorage lentValue :=
          (Allocates.stores_iff valid allocated).mp sourceStored
        exact Typing.BindingStorageTyped.lent rowFound rfl rfl (FormsLoan.created_reference formed)
          (by simpa only [typeEq] using FormsLoan.referent_addressType formed storedAllocated)
      · intro identity same
        have identityEq : identity = lentAllocated.nextLoan :=
          (Option.some.inj (by simpa only [Authority.parentLoan] using same)).symm
        subst identityEq
        exact ⟨_,rowFound,rfl,rfl⟩

/-- The binding emitted by one owned-resident handoff is framed: its fresh
destination is storage-typed and the owner authority carries no row. -/
theorem OutputFramed.of_ownedTransfer {program : RuntimeProgram} {activation scope region : Identity}
    {before after allocated : World} {input : InvocationInput} {layout : Layout} {address : Address}
    (valid : before.WellFormed) (_owned : input.access = .owned)
    (allocation : Allocates program.declarations before (.localSlot activation scope) region
      input.formal.type layout input.formal.mutable address allocated)
    (transferred : Transfers program allocated input.authority input.storage address after) :
    OutputFramed program after input ⟨input.formal.key,address,.owner⟩ := by
  refine ⟨rfl,?_,?_⟩
  · intro _
    exact transferred.bindingStorageTyped (Allocates.wellFormed valid allocation)
      (Allocates.created_bindingStorageTyped allocation)
  · intro identity same
    exact absurd (by simpa only [Authority.parentLoan] using same) (by simp)


/-- Every actual binding rule emits a framed binding: the six rule-specific
producers composed under one dispatcher. -/
theorem BindsInputAt.outputFramed {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : InvocationInput}
    {binding : Binding} (valid : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding after) :
    OutputFramed program after input binding := by
  cases bound with
  | lent ready borrowed resident stored initialized type permission lent =>
      exact OutputFramed.of_lendsResident valid borrowed
        (fun v h => by
          rw [World.Stores] at h stored
          rw [Option.some.inj (h.symm.trans stored)]
          exact type)
        lent
  | owned ready owning resident stored type allocated transferred =>
      exact OutputFramed.of_ownedTransfer valid owning allocated transferred
  | storage ready formal locatedType claimed =>
      exact OutputFramed.of_storageClaim valid formal claimed
  | allocation ready formal owning locatedType transferred =>
      exact OutputFramed.of_allocationTransfer valid formal owning ready transferred
  | guardedAllocation ready formal owning authorityEq locatedType claimed =>
      exact OutputFramed.of_guardedClaim valid formal owning claimed
  | loan ready formal owning locatedType transferred =>
      exact OutputFramed.of_storageLoanTransfer valid formal owning ready transferred


end Kernel

/-- The ordered batch invariant: what is still pending is ready, requested and
framed, the pending heads are pairwise independent, and every binding already
emitted is still framed in the current world. -/
structure Kernel.BatchPrepared (program : RuntimeProgram) (footprint : List Address) (region : Identity)
    (world : World) (pending : List InvocationInput) (outputs : List (Binding × InvocationInput)) : Prop where
  ready : InvocationInputsReadyFor program world footprint pending
  requests : ∀ input ∈ pending, InvocationInput.StorageRequest program world region input
  facts : ∀ input ∈ pending, InputFramed program world input
  independent : ∀ head ∈ pending, ∀ other ∈ pending, head ≠ other →
    head.IndependentOf program footprint world other
  nodup : pending.Nodup
  outputs : ∀ place ∈ outputs, OutputFramed program world place.2 place.1

theorem Kernel.BatchPrepared.nil {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {world : World}
    (ready : InvocationInputsReadyFor program world footprint []) :
    BatchPrepared program footprint region world [] [] := by
  refine ⟨ready,?_,?_,?_,?_,?_⟩
  · intro input member; cases member
  · intro input member; cases member
  · intro head member; cases member
  · exact List.nodup_nil
  · intro place member; cases member

/-- One binding step consumes the head of the pending batch and re-establishes
the whole invariant at the middle world: the remaining inputs are observed, the
head's own output and every earlier output are framed. -/
theorem Kernel.BatchPrepared.step {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before middle : World}
    {input : InvocationInput} {binding : Binding} {pending : List InvocationInput}
    {outputs : List (Binding × InvocationInput)}
    (valid : before.WellFormed) (middleValid : middle.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding middle)
    (prepared : BatchPrepared program footprint region before (input :: pending) outputs) :
    BatchPrepared program footprint region middle pending (⟨binding,input⟩ :: outputs) := by
  have frame : StepFrame before middle := BindsInputAt.stepFrame valid bound
  have observe : ∀ other ∈ pending, input ≠ other →
      StepObservation program footprint region before middle other :=
    fun other member different =>
      BindsInputAt.stepObservation valid bound
        (prepared.independent input List.mem_cons_self other (List.mem_cons_of_mem input member) different)
        (prepared.ready.2.2 other (List.mem_cons_of_mem input member)).1
        (prepared.facts other (List.mem_cons_of_mem input member)).1
        (prepared.facts other (List.mem_cons_of_mem input member)).2.1
        (fun address present => prepared.ready.1 address
          (List.mem_flatMap.mpr ⟨input,List.mem_cons_self,present⟩))
        (prepared.facts other (List.mem_cons_of_mem input member)).2.2
  have absent : input ∉ pending := (List.nodup_cons.mp prepared.nodup).1
  have separate : ∀ other ∈ pending, input ≠ other :=
    fun other member same => absent (same ▸ member)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro address present
      obtain ⟨other,otherMember,present⟩ := List.mem_flatMap.mp present
      exact prepared.ready.1 address (List.mem_flatMap.mpr ⟨other,List.mem_cons_of_mem input otherMember,present⟩)
    · have separated := prepared.ready.2.1
      rw [List.flatMap_cons] at separated
      exact (List.pairwise_append.mp separated).2.1
    · intro other member
      refine ⟨InvocationInput.readyFor_of_observation
        (observe other member (separate other member)) (prepared.ready.2.2 other
          (List.mem_cons_of_mem input member)).1,?_⟩
      exact (prepared.ready.2.2 other (List.mem_cons_of_mem input member)).2
  · intro other member
    exact InvocationInput.storageRequest_of_observation (observe other member (separate other member))
      (prepared.requests other (List.mem_cons_of_mem input member))
  · intro other member
    exact InputFramed.frame (observe other member (separate other member))
      (prepared.facts other (List.mem_cons_of_mem input member))
  · intro head headMember other otherMember different
    exact InvocationInput.IndependentOf.frame valid middleValid frame
      (observe other otherMember (separate other otherMember))
      (prepared.facts head (List.mem_cons_of_mem input headMember)).1
      (prepared.facts other (List.mem_cons_of_mem input otherMember)).1
      (prepared.facts other (List.mem_cons_of_mem input otherMember)).2.1
      (prepared.facts other (List.mem_cons_of_mem input otherMember)).2.2
      (prepared.independent head (List.mem_cons_of_mem input headMember) other
        (List.mem_cons_of_mem input otherMember) different)
  · exact (List.nodup_cons.mp prepared.nodup).2
  · intro place placeMember
    rcases List.mem_cons.mp placeMember with same | member
    · subst same
      exact BindsInputAt.outputFramed valid bound
    · exact OutputFramed.frame valid bound (prepared.outputs place member)

/-- The ordered fold: it either completes every pending binding or stops at the
first genuinely exhausted input, and every binding it has emitted is still
framed in the world it stopped at. -/
theorem Kernel.BatchPrepared.attemptFor {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} :
    ∀ (world : World) (pending : List InvocationInput) (outputs : List (Binding × InvocationInput)),
      world.WellFormed →
      BatchPrepared program footprint region world pending outputs →
      ∃ environment after outcome,
        BindsInputsAttemptFor program recipient activation scope region footprint world pending
          environment after outcome ∧
        ∀ place ∈ outputs, OutputFramed program after place.2 place.1 := by
  intro world pending
  induction pending generalizing world with
  | nil =>
      intro outputs valid prepared
      exact ⟨[],world,.complete,.nil,prepared.outputs⟩
  | cons input rest ih =>
      intro outputs valid prepared
      have headReady : input.Ready program world := prepared.ready.member List.mem_cons_self
      rcases BindsInputAt.success_or_exhausted valid headReady
        (prepared.requests input List.mem_cons_self) with ⟨binding,middle,bound⟩ | exhausted
      · have middleValid : middle.WellFormed :=
          BindsInputAt.wellFormed (recipient := recipient) (activation := activation)
            (scope := scope) (region := region) (input := input) (binding := binding) bound valid
        obtain ⟨environment,after,outcome,attempt,framed⟩ :=
          ih middle (⟨binding,input⟩ :: outputs) middleValid (prepared.step valid middleValid bound)
        exact ⟨binding :: environment,after,outcome,.cons prepared.ready bound attempt,
          fun place member => framed place (List.mem_cons_of_mem _ member)⟩
      · exact ⟨[],world,.exhausted,.exhausted prepared.ready exhausted,prepared.outputs⟩


theorem Kernel.BatchPrepared.of_compatible {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {world : World} {inputs : List InvocationInput}
    (compatible : InvocationInputsCompatible program footprint region world inputs)
    (facts : ∀ input ∈ inputs, InputFramed program world input) (nodup : inputs.Nodup) :
    BatchPrepared program footprint region world inputs [] := by
  refine ⟨compatible.ready,compatible.requests,facts,?_,nodup,?_⟩
  · intro head headMember other otherMember different
    exact compatible.independent headMember otherMember different
  · intro place member
    cases member


/-- The actual successor of a consumed receiver shell: the marked shell the
preparation installed is stored at the receiver port, so the retirement is a
real world write at that exact address - no successor is assumed. -/
theorem Execution.FinishesReceiver.owned_of_stored {world : World} {receiver : ResolvedPlace}
    {value : Value} (stored : world.Stores receiver.address value)
    (marked : value.shellLive = false)
    (callable : ∃ identity arguments, value.head = .callable identity arguments)
    (holes : ∀ field ∈ value.fields, field = none) (resources : value.resources = [])
    (permitted : Permitted world receiver.authority .owned receiver.address) :
    ∃ after, Execution.FinishesReceiver world receiver .owned after := by
  obtain ⟨after,cleared⟩ := stored.write_exists none
  exact ⟨after,.owned stored marked callable holes resources permitted cleared⟩

/-- Address overlap is symmetric, so an apartness obligation can be read from
either side. -/
theorem Address.not_overlaps_symm {first second : Address} (apart : ¬ first.Overlaps second) :
    ¬ second.Overlaps first :=
  fun overlap => apart ⟨overlap.1.symm,overlap.2.1.symm,
    overlap.2.2.elim (fun same => Or.inr same) (fun same => Or.inl same)⟩

/-- The two whole-allocation handoffs leave the roots table alone, so the
receiver's stored shell crosses them unchanged: the congruence that lets the
allocation and loan bindings keep every shell slot exactly as the binding found
it. -/
theorem Kernel.TransfersAllocation.stores {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersAllocation recipient before place after)
    {address : Address} {value : Value} (stored : before.Stores address value) :
    after.Stores address value :=
  World.Stores.of_roots (TransfersAllocation.roots_eq moved) stored

theorem Kernel.TransfersStorageLoan.stores {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersStorageLoan recipient before place after)
    {address : Address} {value : Value} (stored : before.Stores address value) :
    after.Stores address value :=
  World.Stores.of_roots (TransfersStorageLoan.roots_eq moved) stored

/-- An allocation writes one fresh root into the roots table, so every other
address's row is untouched: the transport that carries the receiver's shell
across the allocation a lending or binding performs. This is what lets the
lent binding's own allocation leave the receiver's stored shell alone. -/
theorem Kernel.Allocates.stores_other {program : RuntimeProgram} {before after : World}
    {home : Home} {region : Identity} {type : Term} {layout : Layout} {mutable : Bool}
    {address observed : Address} {shell : Value}
    (allocated : Allocates program.declarations before home region type layout mutable address after)
    (stored : before.Stores observed shell) (different : address.root ≠ observed.root) :
    after.Stores observed shell := by
  rw [World.Stores] at stored ⊢
  cases allocated with
  | fresh =>
      unfold World.read World.root
      rw [Table.get_set_other _ _ _ _ (Ne.symm different)]
      exact stored

/-- A formed loan writes only the vacant destination, so an address apart from
that destination keeps its row: the congruence the borrowed-capture binding needs
after its own allocation. -/
theorem Kernel.FormsLoan.stores_other {program : RuntimeProgram} {purpose : LoanPurpose}
    {before after : World} {authority : Authority} {mode : Mutability} {region : Identity}
    {referent destination : Address}
    (formed : FormsLoan program purpose before authority mode region referent destination after)
    {observed : Address} {shell : Value} (stored : before.Stores observed shell)
    (apart : ¬ destination.Overlaps observed) :
    after.Stores observed shell := by
  cases formed with
  | borrow _ _ _ _ _ _ _ _ _ _ written => exact stored.write_other written apart

/-- A borrowed capture keeps the receiver's row: the lend's own allocation is
transported by the fresh-root fact and its loan formation writes only the fresh
handle, which is apart from the receiver because the handle sits at the
allocation world's next root. -/
theorem Kernel.LendsResident.stores {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {address : Address} {authority otherAuthority : Authority}
    {access : Access} {lease : Option InvocationLease}
    (lent : LendsResident program activation scope region before address authority access lease
      otherAuthority after)
    {observed : Address} {shell : Value} (stored : before.Stores observed shell)
    (different : before.nextRoot ≠ observed.root) :
    after.Stores observed shell := by
  cases lent with
  | owned => exact stored
  | lent _ _ _ allocatedRule formed =>
      have freshRoot := (Allocates.fresh_root allocatedRule).1
      have allocStored := Kernel.Allocates.stores_other allocatedRule stored
        (by rw [freshRoot]; exact different)
      exact Kernel.FormsLoan.stores_other formed allocStored
        (World.not_overlaps_of_root_ne (by rw [freshRoot]; exact different))

/-- Every actual binding rule advances the storage frontier by at most the fresh
root a resident allocation consumes. -/
theorem Kernel.BindsInputAt.nextRoot_le {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : InvocationInput}
    {binding : Binding}
    (bound : BindsInputAt program recipient activation scope region before input binding after) :
    before.nextRoot ≤ after.nextRoot := by
  cases input with
  | mk origin inputFormal inputStorage inputAuthority inputAccess =>
  cases bound with
  | lent ready borrowed resident stored initialized type permission lent =>
      cases lent with
      | owned => exact Nat.le_refl _
      | lent modes sourceStored borrowRegion allocProof formed =>
          rw [Glorious.Language.FormsLoan.nextRoot formed, (Allocates.fresh_root allocProof).2]
          exact Nat.le_succ _
  | owned ready owning resident stored type allocation transferred =>
      rw [Glorious.Language.Transfers.nextRoot transferred, (Allocates.fresh_root allocation).2]
      exact Nat.le_succ _
  | storage ready formal locatedType claimed =>
      exact Nat.le_of_eq (ClaimsStorage.nextRoot claimed).symm
  | allocation ready formal owning locatedType transferred =>
      exact Nat.le_of_eq (TransfersAllocation.nextRoot transferred).symm
  | guardedAllocation ready formal owning authorityEq locatedType claimed =>
      exact Nat.le_of_eq (ClaimsAllocation.nextRoot claimed).symm
  | loan ready formal owning locatedType transferred =>
      exact Nat.le_of_eq (TransfersStorageLoan.nextRoot transferred).symm

end Glorious.Language

namespace Glorious.Language

open Kernel

private theorem initialized_not_prefix_marked {world : World} {source receiver : Address}
    {value shell : Value} (sourceStored : world.Stores source value)
    (initialized : value.Initialized) (stored : world.Stores receiver shell)
    (marked : shell.shellLive = false) : ¬ source.Prefix receiver := by
  intro included
  obtain ⟨suffix,rfl⟩ := Address.prefix_extension included
  change world.read _ = some shell at stored
  rw [World.read_append,sourceStored] at stored
  have inside : value.atPath suffix = some shell := stored
  have live := (initialized suffix shell (ResidentAt.iff_atPath.mpr inside)).1
  rw [marked] at live
  cases live

/-- An input can clear a captured child, but cannot clear an ancestor of the
already-consumed receiver: its actual source must still be initialized. Fresh
installs cannot overwrite the receiver either. This works at arbitrary depth. -/
theorem Kernel.BindsInputAt.marked_shell {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : InvocationInput}
    {binding : Binding} {receiver : Address} {shell : Value}
    (valid : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (stored : before.Stores receiver shell) (marked : shell.shellLive = false) :
    ∃ changed, after.Stores receiver changed ∧ changed.shell = shell.shell := by
  have frontier : receiver.root < before.nextRoot := by
    obtain ⟨root,found,_⟩ := Option.bind_eq_some_iff.mp stored
    exact World.root_bound valid (World.root_found found).1
  cases bound with
  | lent _ _ _ _ _ _ _ lent =>
      exact ⟨shell,Kernel.LendsResident.stores lent stored (Ne.symm (Nat.ne_of_lt frontier)),rfl⟩
  | owned ready owning resident sourceStored sourceType allocated transferred =>
      rename_i destination allocatedWorld layout value
      have allocatedStored := (allocated.read valid receiver).trans stored
      have fresh : ¬ destination.Overlaps receiver := by
        exact World.not_overlaps_of_root_ne
          (by rw [allocated.fresh_root.1]; exact Ne.symm (Nat.ne_of_lt frontier))
      cases transferred with
      | move source initialized _ _ _ _ _ clear install =>
          have unchanged := World.write_read_shell clear
            (initialized_not_prefix_marked source initialized allocatedStored marked)
          rw [allocatedStored] at unchanged
          simp only [Option.map_some] at unchanged
          rw [← World.write_disjoint install fresh] at unchanged
          exact Option.map_eq_some_iff.mp unchanged
  | storage _ _ _ claimed =>
      cases claimed
      exact ⟨shell,stored,rfl⟩
  | allocation _ _ _ _ transferred =>
      exact ⟨shell,Kernel.TransfersAllocation.stores transferred stored,rfl⟩
  | guardedAllocation _ _ _ _ _ claimed =>
      cases claimed
      exact ⟨shell,stored,rfl⟩
  | loan _ _ _ _ transferred =>
      exact ⟨shell,Kernel.TransfersStorageLoan.stores transferred stored,rfl⟩

/-- Binding never refills an old absent address. Owned inputs only clear old
storage; all resident installs occur at the fresh root. -/
theorem Kernel.BindsInputAt.read_none {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : InvocationInput}
    {binding : Binding} {address : Address} (valid : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (frontier : address.root < before.nextRoot) (absent : before.read address = none) :
    after.read address = none := by
  cases bound with
  | lent _ notOwned _ _ _ _ _ lent =>
      cases input with
      | mk origin formal storage authority access =>
      cases lent with
      | owned => exact absurd rfl notOwned
      | lent modes sourceStored borrowRegion allocated formed =>
          rename_i mode value destination allocatedWorld layout sourceRegion
          have missing := (allocated.read valid address).trans absent
          have fresh : ¬ destination.Overlaps address := by
            exact World.not_overlaps_of_root_ne
              (by rw [allocated.fresh_root.1]; exact Ne.symm (Nat.ne_of_lt frontier))
          cases formed with
          | borrow _ _ _ _ _ _ _ _ _ _ written =>
              exact (World.write_disjoint written fresh).trans missing
  | owned ready owning resident sourceStored sourceType allocated transferred =>
      rename_i destination allocatedWorld layout value
      have missing := (allocated.read valid address).trans absent
      have fresh : ¬ destination.Overlaps address := by
        exact World.not_overlaps_of_root_ne
          (by rw [allocated.fresh_root.1]; exact Ne.symm (Nat.ne_of_lt frontier))
      cases transferred with
      | move _ _ _ _ _ _ _ clear install =>
          exact (World.write_disjoint install fresh).trans (World.clear_absent clear missing)
  | storage _ _ _ claimed => cases claimed; exact absent
  | allocation _ _ _ _ transferred =>
      simpa only [World.read,World.root,Glorious.Language.TransfersAllocation.roots_eq transferred] using absent
  | guardedAllocation _ _ _ _ _ claimed => cases claimed; exact absent
  | loan _ _ _ _ transferred =>
      simpa only [World.read,World.root,Glorious.Language.TransfersStorageLoan.roots_eq transferred] using absent

/-- The actual owned resident binding empties its source. -/
theorem Kernel.BindsInputAt.owned_cleared {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : InvocationInput}
    {binding : Binding}
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (owned : input.access = .owned) (resident : input.formal.IsResident) :
    after.read input.storage = none := by
  cases bound with
  | lent _ notOwned _ _ _ _ _ _ => exact absurd owned notOwned
  | owned _ _ _ _ _ _ transferred =>
      cases transferred with
      | move _ _ _ _ _ apart _ clear install =>
          have empty := World.write_read_inside clear []
          simp only [List.append_nil] at empty
          exact (World.write_disjoint install (Address.not_overlaps_symm apart)).trans empty
  | storage _ formal _ _ => rw [formal] at resident; exact resident.elim
  | allocation _ formal _ _ _ => rw [formal] at resident; exact resident.elim
  | guardedAllocation _ formal _ _ _ _ => rw [formal] at resident; exact resident.elim
  | loan _ formal _ _ _ => rw [formal] at resident; exact resident.elim

end Glorious.Language

namespace Glorious.Language

open Kernel

theorem Kernel.BindsInputsAttemptFor.read_none {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {inputs : List InvocationInput} {bindings : Environment} {outcome : PreparationOutcome}
    {address : Address} (valid : before.WellFormed)
    (attempt : BindsInputsAttemptFor program recipient activation scope region footprint
      before inputs bindings after outcome)
    (frontier : address.root < before.nextRoot) (absent : before.read address = none) :
    after.read address = none := by
  induction attempt with
  | nil => exact absent
  | cons _ first _ ih =>
      exact ih (first.wellFormed valid) (Nat.lt_of_lt_of_le frontier first.nextRoot_le)
        (first.read_none valid frontier absent)
  | exhausted => exact absent

theorem Kernel.BindsInputsAttemptFor.marked_shell {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {inputs : List InvocationInput} {bindings : Environment} {outcome : PreparationOutcome}
    {receiver : Address} {shell : Value} (valid : before.WellFormed)
    (attempt : BindsInputsAttemptFor program recipient activation scope region footprint
      before inputs bindings after outcome)
    (stored : before.Stores receiver shell) (marked : shell.shellLive = false) :
    ∃ changed, after.Stores receiver changed ∧ changed.shell = shell.shell := by
  induction attempt generalizing shell with
  | nil => exact ⟨shell,stored,rfl⟩
  | cons _ first _ ih =>
      obtain ⟨middle,middleStored,same⟩ := first.marked_shell valid stored marked
      have middleMarked : middle.shellLive = false := by
        have live := congrArg Value.shellLive same
        simpa only [Value.shell,Value.withFields,Value.shellLive] using live.trans marked
      obtain ⟨changed,found,last⟩ := ih (first.wellFormed valid) middleStored middleMarked
      exact ⟨changed,found,last.trans same⟩
  | exhausted => exact ⟨shell,stored,rfl⟩

/-- Every owned resident source in a completed batch is absent afterwards,
including sources bound before arbitrary ordinary or erased-resource inputs. -/
theorem Kernel.BindsInputsAttemptFor.owned_cleared {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {inputs : List InvocationInput} {bindings : Environment} {outcome : PreparationOutcome}
    {input : InvocationInput} (valid : before.WellFormed)
    (attempt : BindsInputsAttemptFor program recipient activation scope region footprint
      before inputs bindings after outcome) (complete : outcome = .complete)
    (frontier : input.storage.root < before.nextRoot) (member : input ∈ inputs)
    (owned : input.access = .owned) (resident : input.formal.IsResident) :
    after.read input.storage = none := by
  induction attempt with
  | nil => cases member
  | cons _ first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact rest.read_none (first.wellFormed valid)
          (Nat.lt_of_lt_of_le frontier first.nextRoot_le) (first.owned_cleared owned resident)
      · exact ih (first.wellFormed valid) complete
          (Nat.lt_of_lt_of_le frontier first.nextRoot_le) later
  | exhausted => cases complete

end Glorious.Language


namespace Glorious.Language

open Kernel

/-- The batch's existing fresh-row observation, specialized to one retained
permission. It refers only to the current source geometry, loan modes and guards. -/
def Kernel.InvocationInput.PermissionCompatible (world : World) (input : InvocationInput)
    (authority : Authority) (access : Access) (address : Address) : Prop :=
  ∀ referent mode guards kind, input.FreshRow world referent mode guards kind →
    authority.LoanCompatible world access address referent mode guards


theorem Kernel.InvocationInput.PermissionCompatible.frame {before after : World}
    {input : InvocationInput} {authority : Authority} {access : Access} {address : Address}
    (valid : before.WellFormed) (frame : StepFrame before after)
    (inputRecorded : input.authority.Recorded before.loans)
    (recorded : authority.Recorded before.loans)
    (compatible : input.PermissionCompatible before authority access address) :
    input.PermissionCompatible after authority access address := by
  intro referent mode guards kind fresh
  exact Kernel.Authority.LoanCompatible.frame valid frame recorded
    (compatible referent mode guards kind (InvocationInput.FreshRow.frame valid frame inputRecorded fresh))

/-- Exact source-state fresh-row compatibility preserves the receiver's
permission through every resident and erased-resource binding constructor. -/
theorem Kernel.BindsInputAt.permitted {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : InvocationInput}
    {binding : Binding} {authority : Authority} {access : Access} {address : Address}
    (valid : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (permission : Permitted before authority access address)
    (compatible : input.PermissionCompatible before authority access address) :
    Permitted after authority access address := by
  cases bound with
  | lent ready borrowed resident stored initialized type allowed lent =>
      cases input with
      | mk origin formal storage inputAuthority inputAccess =>
      cases lent with
      | owned => exact absurd rfl borrowed
      | lent modes sourceStored borrowRegion allocated formed =>
          rename_i mode value destination allocatedWorld layout sourceRegion
          have fresh : InvocationInput.FreshRow before ⟨origin,formal,storage,inputAuthority,inputAccess⟩
              storage mode (inputAuthority.guardLoans before) .restoring := by
            cases formal <;> simp only [InputFormal.IsResident] at resident
            all_goals try contradiction
            rcases modes with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
              simp [InvocationInput.FreshRow]
          have prior := permission.locationExtension (allocated.locationExtension valid) allocated.loans
          apply formed.permitted (allocated.wellFormed valid) prior
          rw [Authority.guardLoans.loans_congr allocated.loans]
          exact Authority.LoanCompatible.loans_congr allocated.loans
            (compatible storage mode (inputAuthority.guardLoans before) .restoring fresh)
  | owned _ _ _ _ _ allocated transferred =>
      exact (permission.locationExtension (allocated.locationExtension valid) allocated.loans).locationExtension
        (.of_locations transferred.locations) transferred.loans
  | storage _ formal _ claimed =>
      apply claimed.permitted valid permission
      exact compatible _ _ _ .storageBorrow (by simp [InvocationInput.FreshRow,formal])
  | allocation _ _ _ _ transferred =>
      exact Permitted.of_rows (Glorious.Language.TransfersAllocation.row_relation transferred)
        (fun observed root found => ⟨root,by
          simpa only [World.root,Glorious.Language.TransfersAllocation.roots_eq transferred] using found⟩)
        permission
  | guardedAllocation _ formal _ authorityEq _ claimed =>
      apply claimed.permitted valid permission
      apply compatible _ _ _ .owning
      simp only [InvocationInput.FreshRow,formal]
      exact ⟨⟨_,_,authorityEq⟩,by trivial⟩
  | loan _ _ _ _ transferred =>
      exact Permitted.of_rows (Glorious.Language.TransfersStorageLoan.row_relation transferred)
        (fun observed root found => ⟨root,by
          simpa only [World.root,Glorious.Language.TransfersStorageLoan.roots_eq transferred] using found⟩)
        permission

/-- One source-state compatibility check covers the complete ordered batch;
there is no future-world permission callback. -/
theorem Kernel.BindsInputsAttemptFor.permitted {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {inputs : List InvocationInput} {bindings : Environment} {outcome : PreparationOutcome}
    {authority : Authority} {access : Access} {address : Address} (valid : before.WellFormed)
    (attempt : BindsInputsAttemptFor program recipient activation scope region footprint
      before inputs bindings after outcome)
    (permission : Permitted before authority access address)
    (recorded : ∀ input ∈ inputs, input.authority.Recorded before.loans)
    (compatible : ∀ input ∈ inputs, input.PermissionCompatible before authority access address) :
    Permitted after authority access address := by
  induction attempt with
  | nil => exact permission
  | cons _ first _ ih =>
      have frame := first.stepFrame valid
      apply ih (first.wellFormed valid)
        (first.permitted valid permission (compatible _ List.mem_cons_self))
      · intro input member
        exact (recorded input (List.mem_cons_of_mem _ member)).transport
          (fun id loan found => let ⟨current,selected,_⟩ := StepFrame.row_of_before valid frame found; ⟨current,selected⟩)
      · intro input member
        exact (compatible input (List.mem_cons_of_mem _ member)).frame valid frame
          (recorded input (List.mem_cons_of_mem _ member)) permission.recorded
  | exhausted => exact permission

end Glorious.Language


namespace Glorious.Language

open Kernel

/-- The actual call publishes the resident recipe, including zero captures. -/
theorem Execution.LocalStep.call_ready {program : Kernel.Program} {before after : Execution.State}
    {declaration : DeclId} {inputs : List InvocationInput} {caller : Execution.Context}
    {function : Function} {source : Execution.EntrySource} {tail : Bool}
    (called : Execution.LocalStep program before (some (.call declaration inputs)) after)
    (entry : after.task = .enter caller function source tail) :
    source.Ready program after.world function := by
  cases called with
  | call _ _ _ receiver selected _ _ _ _ =>
      rcases Execution.Task.enter.inj entry with ⟨rfl,rfl,rfl,rfl⟩
      exact ⟨_,_,receiver,selected⟩

/-- Preparation publishes the marked shell and its complete resident capture
inventory. Fields remain occupied here; their holes must be produced by binding. -/
def Execution.ReceiverPrepared (world : World) (receiver : ResolvedPlace)
    (inputs : List InvocationInput) : Prop :=
  ∃ shell, world.Stores receiver.address shell ∧ shell.shellLive = false ∧
    (∃ id arguments, shell.head = .callable id arguments) ∧ shell.resources = [] ∧
    Permitted world receiver.authority .owned receiver.address ∧
    ∀ index, index < shell.fields.length → ∃ input ∈ inputs,
      input.storage = receiver.address.child index ∧ input.access = .owned ∧ input.formal.IsResident

/-- A completed actual binder retires its prepared receiver. The stored shell,
all capture holes, owning permission and final write are derived here. -/
theorem Kernel.BindsInputsAttemptFor.finishesReceiver {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {inputs : List InvocationInput} {bindings : Environment} {outcome : PreparationOutcome}
    {receiver : ResolvedPlace} (valid : before.WellFormed)
    (attempt : BindsInputsAttemptFor program recipient activation scope region footprint
      before inputs bindings after outcome) (complete : outcome = .complete)
    (prepared : Execution.ReceiverPrepared before receiver inputs)
    (recorded : ∀ input ∈ inputs, input.authority.Recorded before.loans)
    (compatible : ∀ input ∈ inputs,
      input.PermissionCompatible before receiver.authority .owned receiver.address) :
    ∃ consumed, Execution.FinishesReceiver after receiver .owned consumed := by
  obtain ⟨shell,stored,marked,head,resources,permission,covers⟩ := prepared
  obtain ⟨changed,found,same⟩ := attempt.marked_shell valid stored marked
  have live : changed.shellLive = false := by
    have projected := congrArg Value.shellLive same
    simpa only [Value.shell,Value.withFields,Value.shellLive] using projected.trans marked
  have changedHead : changed.head = shell.head := by
    simpa only [Value.shell,Value.withFields,Value.head] using congrArg Value.head same
  have emptyResources : changed.resources = [] := by
    have projected := congrArg Value.resources same
    simpa only [Value.shell,Value.withFields,Value.resources] using projected.trans resources
  have length : changed.fields.length = shell.fields.length := by
    simpa only [Value.shell,Value.withFields,Value.fields,List.length_replicate] using
      congrArg (fun value => value.fields.length) same
  have holes : ∀ field ∈ changed.fields, field = none := by
    intro field member
    cases field with
    | none => rfl
    | some value =>
        obtain ⟨index,atField⟩ := List.mem_iff_getElem?.mp member
        have indexBound : index < shell.fields.length := by
          rw [← length]
          exact (List.getElem?_eq_some_iff.mp atField).1
        obtain ⟨input,member,atStorage,owned,resident⟩ := covers index indexBound
        have frontier : input.storage.root < before.nextRoot := by
          rw [atStorage]
          obtain ⟨root,rootFound,_⟩ := Option.bind_eq_some_iff.mp stored
          exact World.root_bound valid (World.root_found rootFound).1
        have cleared := attempt.owned_cleared valid complete frontier member owned resident
        rw [atStorage] at cleared
        have child : after.read (receiver.address.child index) = some value := by
          simp [Address.child,World.read_append,
            (show after.read receiver.address = some changed from found),Value.atPath,atField]
        have impossible := child.symm.trans cleared
        cases impossible
  exact Execution.FinishesReceiver.owned_of_stored found live
    (by simpa only [changedHead] using head) holes emptyResources
    (attempt.permitted valid permission recorded compatible)

end Glorious.Language


namespace Glorious.Language
open Kernel

theorem Execution.ConsumesReceiver.owned_stores {before after : World} {address : Address}
    {authority : Authority} {value : Value} (consumed : Execution.ConsumesReceiver before address authority .owned after)
    (stored : before.Stores address value) :
    ∃ shell, after.Stores address shell ∧ shell.shellLive = false ∧ shell.head = value.head ∧
      shell.fields = value.fields ∧ shell.resources = value.resources ∧ Permitted after authority .owned address := by
  cases consumed with
  | lent impossible => exact False.elim (impossible rfl)
  | owned found _ _ permission written =>
      cases Option.some.inj (found.symm.trans stored)
      refine ⟨.resident value.owner value.type value.head false value.fields value.resources,?_,rfl,rfl,rfl,rfl,?_⟩
      · have reading := World.write_read_inside written []
        simp only [List.append_nil] at reading
        exact reading
      · exact permission.locationExtension (.of_locations (World.write_locations written)) (World.write_loans written)

theorem Execution.ConsumesAvailability.marked_shell {before after : World} {address receiver : Address}
    {authority : Authority} {id : Identity} {access : Access} {shell : Value}
    (consumed : Execution.ConsumesAvailability before address authority id access after)
    (stored : before.Stores receiver shell) (marked : shell.shellLive = false) :
    ∃ changed, after.Stores receiver changed ∧ changed.shell = shell.shell := by
  cases consumed with
  | lent => exact ⟨shell,stored,rfl⟩
  | owned sourceStored initialized _ _ _ _ written =>
      have preserved := World.write_read_shell written
        (initialized_not_prefix_marked sourceStored initialized stored marked)
      rw [show before.read receiver = some shell from stored] at preserved
      obtain ⟨changed,found,same⟩ := Option.map_eq_some_iff.mp preserved
      exact ⟨changed,found,same⟩

theorem Execution.ResidentCaptureInputs.covers {receiver : Address} {authority : Authority}
    {formals : List Local} {index : Nat} (bounded : index < formals.length) :
    ∃ input ∈ Execution.ResidentCaptureInputs receiver authority .owned formals,
      input.storage = receiver.child index ∧ input.access = .owned ∧ input.formal.IsResident := by
  refine ⟨⟨.capture index,.resident formals[index],receiver.child index,authority,.owned⟩,?_,rfl,rfl,True.intro⟩
  apply List.mem_map.mpr
  refine ⟨(formals[index],index),?_,rfl⟩
  apply List.mem_iff_getElem?.mpr
  exact ⟨index,by simp only [List.getElem?_zipIdx,List.getElem?_eq_getElem bounded,Option.map_some,Nat.zero_add]⟩

/-- Actual resident preparation retains the full indexed capture inventory. -/
theorem Execution.PreparesEntry.resident_receiver {program : Kernel.Program} {callee : Execution.Context}
    {function : Function} {before after : World} {receiver : ResolvedPlace}
    {arguments inputs : List InvocationInput} (typed : Typing.WorldTyped program before)
    (prepares : Execution.PreparesEntry program callee function before (.resident receiver .owned arguments) inputs after) :
    Execution.ReceiverPrepared after receiver inputs := by
  cases prepares with
  | resident callable selected lent captures consumed =>
      cases lent with
      | lent modes => rcases modes with ⟨impossible,_⟩ | ⟨impossible,_⟩ <;> cases impossible
      | owned =>
          obtain ⟨value,stored,_,head,_,_⟩ := callable
          have shape := (typed.2.1 _ _ (World.resident_iff_stores.mpr stored)).callable_shape head selected
          obtain ⟨shell,found,marked,sameHead,fields,resources,permission⟩ := consumed.owned_stores stored
          refine ⟨shell,found,marked,⟨_,_,sameHead.trans head⟩,resources.trans shape.2.1,permission,?_⟩
          intro index bounded
          rw [fields,shape.2.2] at bounded
          obtain ⟨input,member,storage,owned,resident⟩ := Execution.ResidentCaptureInputs.covers
            (receiver := receiver.address) (authority := receiver.authority) bounded
          exact ⟨input,List.mem_append_left _ (captures.1.symm ▸ member),storage,owned,resident⟩

/-- Contextual preparation preserves its actual code-only receiver, including
when witness consumption clears storage after the receiver was marked. -/
theorem Execution.PreparesEntry.contextual_receiver {program : Kernel.Program} {callee : Execution.Context}
    {function : Function} {before after : World} {receiver witness : ResolvedPlace} {witnessAccess : Access}
    {sourceInputs inputs : List InvocationInput} (typed : Typing.WorldTyped program before)
    (empty : ∃ value, before.Stores receiver.address value ∧ value.fields = [])
    (prepares : Execution.PreparesEntry program callee function before
      (.contextual receiver .owned witness witnessAccess sourceInputs) inputs after) :
    Execution.ReceiverPrepared after receiver inputs := by
  cases prepares with
  | contextual callable selected _ _ lentReceiver lentWitness _ consumedReceiver consumedAvailability =>
      cases lentReceiver with
      | lent modes => rcases modes with ⟨impossible,_⟩ | ⟨impossible,_⟩ <;> cases impossible
      | owned =>
          obtain ⟨value,stored,_,head,_,_⟩ := callable
          obtain ⟨other,otherStored,empty⟩ := empty
          cases Option.some.inj (stored.symm.trans otherStored)
          have shape := (typed.2.1 _ _ (World.resident_iff_stores.mpr stored)).callable_shape head selected
          have frontier : receiver.address.root < before.nextRoot := by
            obtain ⟨root,rootFound,_⟩ := Option.bind_eq_some_iff.mp stored
            exact World.root_bound typed.1 (World.root_found rootFound).1
          have lentStored := Kernel.LendsResident.stores lentWitness stored (Nat.ne_of_lt frontier).symm
          obtain ⟨shell,found,marked,sameHead,fields,resources,permission⟩ := consumedReceiver.owned_stores lentStored
          obtain ⟨changed,changedStored,same⟩ := consumedAvailability.marked_shell found marked
          have length : changed.fields.length = shell.fields.length := by
            simpa only [Value.shell,Value.withFields,Value.fields,List.length_replicate] using
              congrArg (fun value => value.fields.length) same
          refine ⟨changed,changedStored,?_,?_,?_,?_,?_⟩
          · simpa only [Value.shell,Value.withFields,Value.shellLive] using (congrArg Value.shellLive same).trans marked
          · exact ⟨_,_,by simpa only [Value.shell,Value.withFields,Value.head] using
              (congrArg Value.head same).trans (sameHead.trans head)⟩
          · simpa only [Value.shell,Value.withFields,Value.resources] using
              (congrArg Value.resources same).trans (resources.trans shape.2.1)
          · exact permission.locationExtension (.of_locations consumedAvailability.locations) consumedAvailability.loans
          · intro index bounded
            rw [length,fields,empty] at bounded
            exact False.elim (Nat.not_lt_zero index bounded)

end Glorious.Language


namespace Glorious.Language
open Kernel

/-- The receiver-finishing consumer of the same actual ordered binder. Admission
mentions only original source readiness and fresh-row compatibility at the
prepared world; no completed-world fact is supplied by the caller. -/
theorem Kernel.BindsInputsAttemptFor.finishesEntry {program : Kernel.Program} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {original withRegion prepared bound : World}
    {callee : Execution.Context} {function : Function} {source : Execution.EntrySource}
    {inputs : List InvocationInput} {bindings : Environment}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program original) (ready : source.Ready program original function)
    (fresh : FreshRegion original original.nextRegion withRegion)
    (prepares : Execution.PreparesEntry program callee function withRegion source inputs prepared)
    (attempt : BindsInputsAttemptFor program recipient activation scope region footprint
      prepared inputs bindings bound .complete)
    (recorded : ∀ input ∈ inputs, input.authority.Recorded prepared.loans)
    (compatible : ∀ receiver, source.ownedReceiver = some receiver → ∀ input ∈ inputs,
      input.PermissionCompatible prepared receiver.authority .owned receiver.address) :
    ∃ consumed, Execution.FinishesEntry bound source consumed := by
  have regionTyped := fresh.worldTyped typed
  have preparedTyped := prepares.worldTyped valid inventory regionTyped
  cases source with
  | supplied => exact ⟨bound,.supplied⟩
  | resident receiver access arguments =>
      by_cases owned : access = .owned
      · subst access
        obtain ⟨consumed,finished⟩ := attempt.finishesReceiver preparedTyped.1 rfl
          (prepares.resident_receiver regionTyped) recorded
          (compatible receiver (by simp only [Execution.EntrySource.ownedReceiver,ite_true]))
        exact ⟨consumed,.resident finished⟩
      · exact ⟨bound,.resident (.lent owned)⟩
  | contextual receiver access witness witnessAccess sourceInputs =>
      by_cases owned : access = .owned
      · subst access
        obtain ⟨_,_,_,_,_,_,_,_,_,_,value,stored,empty⟩ := ready
        have regionEmpty : ∃ value, withRegion.Stores receiver.address value ∧ value.fields = [] := by
          rw [fresh.2]
          exact ⟨value,stored,empty⟩
        obtain ⟨consumed,finished⟩ := attempt.finishesReceiver preparedTyped.1 rfl
          (prepares.contextual_receiver regionTyped regionEmpty) recorded
          (compatible receiver (by simp only [Execution.EntrySource.ownedReceiver,ite_true]))
        exact ⟨consumed,.contextual finished⟩
      · exact ⟨bound,.contextual (.lent owned)⟩

/-- Ordinary input-batch preentry progress. The authoritative ordered fold
produces either the first physical exhaustion or a complete batch whose receiver
is actually retired. All receiver shape, capture holes, permission and successor
storage are derived from typing, preparation and the real binding transitions. -/
theorem Kernel.EntryBatch.enterWorldAttempt {program : Kernel.Program} {before : Execution.State}
    {caller : Execution.Context} {function : Function} {source : Execution.EntrySource}
    {withRegion prepared : World} {inputs : List InvocationInput}
    (callee : Execution.Context)
    (calleeLifetime : callee.activation = before.nextActivation ∧
      callee.scope = before.world.nextRegion ∧ callee.region = before.world.nextRegion)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (ready : source.Ready program before.world function)
    (declared : ∃ declaration, program.declarations.function function.declaration = some declaration)
    (prepares : Execution.PreparesEntry program callee function withRegion source inputs prepared)
    (fresh : FreshRegion before.world before.world.nextRegion withRegion)
    (incoming : IncomingResources program function before.world (source.originalInputs function))
    (product : InvocationInputsCompatible program (inputs.flatMap InvocationInput.clearedStorage)
      before.world.nextRegion prepared inputs)
    (receiverCompatible : ∀ receiver, source.ownedReceiver = some receiver → ∀ input ∈ inputs,
      input.PermissionCompatible prepared receiver.authority .owned receiver.address)
    (callerUnsafe : function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) :
    ∃ context after outcome,
      Execution.EnterWorldAttempt program before caller function source context after outcome := by
  obtain ⟨declaration,declared⟩ := declared
  have preparedTyped := prepares.worldTyped valid inventory (fresh.worldTyped typed)
  have facts := product.inputFramed preparedTyped.1
  have keys : (inputs.map (fun input => input.formal.key)).Nodup := by
    rw [prepares.map_inputs (fun input => input.formal.key) (by intros; rfl)]
    exact incoming.1
  have nodup : inputs.Nodup := (List.pairwise_map.mp keys).imp
    (fun different same => different (congrArg (fun input => input.formal.key) same))
  obtain ⟨environment,bound,outcome,attempt,_⟩ :=
    Kernel.BatchPrepared.attemptFor (recipient := .activation before.nextActivation)
      (activation := before.nextActivation) (scope := before.world.nextRegion)
      (region := before.world.nextRegion) prepared inputs [] preparedTyped.1
      (Kernel.BatchPrepared.of_compatible product facts nodup)
  let context : Execution.Context :=
    ⟨environment,declaration.header.module,before.nextActivation,before.world.nextRegion,
      before.world.nextRegion,function.entryScope before.world.nextRegion before.nextBrand,false,
      [⟨function.declaration,environment⟩]⟩
  have transported : Execution.PreparesEntry program context function withRegion source inputs prepared :=
    prepares.callee_context calleeLifetime.1 calleeLifetime.2.1 calleeLifetime.2.2
  cases outcome with
  | complete =>
      obtain ⟨consumed,finished⟩ := attempt.finishesEntry valid inventory typed ready fresh prepares
        (fun input member => (facts input member).1) receiverCompatible
      exact ⟨context,consumed,.complete,
        .inputs declared fresh transported incoming attempt finished rfl callerUnsafe⟩
  | exhausted =>
      exact ⟨context,bound,.exhausted,
        .inputs declared fresh transported incoming attempt rfl rfl callerUnsafe⟩

theorem Kernel.LendsResident.availability {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {source : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease}
    (lent : Kernel.LendsResident program activation scope region before source authority access lease result after) :
    after.availability = before.availability := by
  cases lent with
  | owned => rfl
  | lent _ _ _ allocated formed =>
    cases formed with
    | borrow _ _ _ _ _ _ _ _ _ _ written =>
      obtain ⟨_,_,_,rfl⟩ := World.write_value_update written
      cases allocated
      rfl


namespace Execution

/-- Receiver consumption is a real shell write, or the no-write lending rule.
The successor world is constructed from the original stored receiver. -/
theorem ConsumesReceiver.exists {world : World} {address : Address} {authority : Authority}
    {access : Access} {value : Value} (stored : world.Stores address value)
    (initialized : value.Initialized) (callable : ∃ identity arguments, value.head = .callable identity arguments)
    (permission : Permitted world authority access address) :
    ∃ after, ConsumesReceiver world address authority access after := by
  by_cases owned : access = .owned
  · subst access
    obtain ⟨after,written⟩ := stored.write_exists
      (some (.resident value.owner value.type value.head false value.fields value.resources))
    exact ⟨after,.owned stored (initialized [] value .root).1 callable permission written⟩
  · exact ⟨world,.lent owned⟩

/-- Capture initialization comes from the original ports; their new authority
comes from the actual receiver loan. Neither fact is assumed after lending. -/
theorem LendsReceiver.captureInputs {program : Kernel.Program} {callee : Context}
    {before after : World} {receiver : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} {formals : List Local} {inputs : List InvocationInput}
    (valid : before.WellFormed)
    (lent : LendsReceiver program callee before receiver authority access lease result after)
    (permission : Permitted before authority access receiver)
    (original : CaptureInputs before receiver authority access formals inputs) :
    CaptureInputs after receiver result access formals (ResidentCaptureInputs receiver result access formals) := by
  obtain ⟨rfl,original⟩ := original
  have borrower := lent.borrower_permitted valid permission
  refine ⟨rfl,?_⟩
  intro input member
  obtain ⟨⟨formal,index⟩,paired,rfl⟩ := List.mem_map.mp (show input ∈ formals.zipIdx.map
    (fun (formal,index) => (⟨.capture index,formal,receiver.child index,result,access⟩ : InvocationInput)) from member)
  have prior : (⟨.capture index,formal,receiver.child index,authority,access⟩ : InvocationInput) ∈
      ResidentCaptureInputs receiver authority access formals := List.mem_map.mpr ⟨(formal,index),paired,rfl⟩
  obtain ⟨value,stored,initialized⟩ := (original _ prior).1
  exact ⟨⟨value,lent.stores stored (Nat.ne_of_lt (stored.rooted_bound valid)).symm,initialized⟩,
    borrower.child index⟩

/-- Resident preparation constructs its actual loan, capture authorities, and
receiver-shell mutation, or reports the positive physical allocation failure.
Every premise describes the original world, including the allocation request. -/
theorem PreparesEntryAttempt.resident_progress {program : Kernel.Program} {callee : Context}
    {function : Function} {before : World} {receiver : ResolvedPlace} {access : Access}
    {arguments : List InvocationInput} {identity : DeclId} {instanceArguments : List Term}
    {captures : List InvocationInput} (valid : before.WellFormed)
    (callable : CallableReceiver program before receiver.address receiver.authority access identity instanceArguments)
    (selected : Instance program identity instanceArguments function)
    (original : CaptureInputs before receiver.address receiver.authority access function.captures captures)
    (request : ∀ value, before.Stores receiver.address value →
      Kernel.LendsResident.Request program before callee.region receiver.address receiver.authority access value.type) :
    ∃ inputs after outcome,
      PreparesEntryAttempt program callee function before (.resident receiver access arguments) inputs after outcome := by
  obtain ⟨value,stored,initialized,head,resources,permission⟩ := callable
  have callable : CallableReceiver program before receiver.address receiver.authority access identity instanceArguments :=
    ⟨value,stored,initialized,head,resources,permission⟩
  rcases Kernel.LendsResident.success_or_exhausted (activation := callee.activation) (scope := callee.scope)
      valid stored initialized resources permission (request value stored) with
    ⟨lease,authority,lent,lends⟩ | exhausted
  · have receiverStored := lends.stores stored (Nat.ne_of_lt (stored.rooted_bound valid)).symm
    obtain ⟨after,consumed⟩ := ConsumesReceiver.exists receiverStored initialized ⟨identity,instanceArguments,head⟩
      (lends.borrower_permitted valid permission)
    exact ⟨_,after,.complete,.resident callable selected lends
      (LendsReceiver.captureInputs valid lends permission original) consumed⟩
  · exact ⟨[],before,.exhausted,.residentExhausted callable selected exhausted⟩

theorem LendsReceiver.reservationInputs {program : Kernel.Program} {callee : Context}
    {before after : World} {source : Address} {authority result : Authority} {access incoming : Access}
    {lease : Option InvocationLease} {available : Availability} {formals : List Local}
    {inputs : List InvocationInput} (valid : before.WellFormed)
    (lent : LendsReceiver program callee before source authority access lease result after)
    (original : ReservationInputs before available incoming formals inputs)
    (compatible : access ≠ .owned → ∀ input ∈ inputs,
      input.authority.LoanCompatible before incoming input.storage source
        (if access = .shared then .shared else .unique) (authority.guardLoans before)) :
    ReservationInputs after available incoming formals inputs := by
  refine ⟨original.1,original.2.1,original.2.2.1,?_⟩
  intro input member
  obtain ⟨permission,value,stored,initialized,type⟩ := original.2.2.2 input member
  exact ⟨lent.permitted valid permission (fun borrowed => compatible borrowed input member),
    value,lent.stores stored (Nat.ne_of_lt (stored.rooted_bound valid)).symm,initialized,type⟩

theorem ConsumesReceiver.stores_other {before after : World} {receiver observed : Address}
    {authority : Authority} {access : Access} {value : Value}
    (consumed : ConsumesReceiver before receiver authority access after)
    (stored : before.Stores observed value) (apart : ¬ receiver.Overlaps observed) :
    after.Stores observed value := by
  cases consumed with
  | lent => exact stored
  | owned _ _ _ _ written => exact stored.write_other written apart

theorem ConsumesReceiver.availability {before after : World} {receiver : Address}
    {authority : Authority} {access : Access}
    (consumed : ConsumesReceiver before receiver authority access after) :
    after.availability = before.availability := by
  cases consumed with
  | lent => rfl
  | owned _ _ _ _ written =>
    obtain ⟨_,_,_,rfl⟩ := World.write_value_update written
    rfl

/-- The owned witness is cleared and its actual ledger deactivated. A borrowed
witness is retained. Both successors are constructed from its stored witness. -/
theorem ConsumesAvailability.exists {world : World} {address : Address} {authority : Authority}
    {access : Access} {value : Value} {identity : Identity} {available : Availability}
    (stored : world.Stores address value) (initialized : value.Initialized)
    (head : value.head = .available identity) (selected : world.availability.get identity = some available)
    (active : available.active = true) (permission : Permitted world authority access address) :
    ∃ after, ConsumesAvailability world address authority identity access after := by
  by_cases owned : access = .owned
  · subst access
    obtain ⟨cleared,written⟩ := stored.write_exists none
    exact ⟨_,.owned stored initialized head selected active permission written⟩
  · exact ⟨world,.lent owned⟩


/-- Contextual preparation constructs both ordered leases, transports the
original reservation product, and performs the actual receiver/witness writes.
A second allocation failure retains the first lease. Compatibility, separation,
resource readiness, and requests are all facts about the original world. -/
theorem PreparesEntryAttempt.contextual_progress {program : Kernel.Program} {callee : Context}
    {function : Function} {before : World} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {identity : DeclId} {instanceArguments : List Term}
    {available : Availability} {captures arguments : List InvocationInput} (valid : before.WellFormed)
    (callable : CallableReceiver program before receiver.address receiver.authority receiverAccess identity instanceArguments)
    (selected : Instance program identity instanceArguments function)
    (witnessReady : ContextualWitness before witness witnessAccess available)
    (reserved : ReservationInputs before available witnessAccess function.captures captures)
    (apart : ¬ receiver.address.Overlaps witness.address)
    (receiverRequest : ∀ value, before.Stores receiver.address value →
      Kernel.LendsResident.Request program before callee.region receiver.address receiver.authority receiverAccess value.type)
    (witnessRequest : ∀ value, before.Stores witness.address value →
      Kernel.LendsResident.Request program before callee.region witness.address witness.authority witnessAccess value.type)
    (witnessResources : ∀ value, before.Stores witness.address value → value.ResourcesAccessible program before witnessAccess)
    (witnessCompatible : receiverAccess ≠ .owned → witness.authority.LoanCompatible before witnessAccess
      witness.address receiver.address (if receiverAccess = .shared then .shared else .unique) (receiver.authority.guardLoans before))
    (receiverCompatible : witnessAccess ≠ .owned → receiver.authority.LoanCompatible before receiverAccess
      receiver.address witness.address (if witnessAccess = .shared then .shared else .unique) (witness.authority.guardLoans before))
    (witnessViews : receiverAccess ≠ .owned → ∀ value, before.Stores witness.address value →
      value.ViewsLoanCompatible before witnessAccess receiver.address
        (if receiverAccess = .shared then .shared else .unique) (receiver.authority.guardLoans before))
    (capturesReceiver : receiverAccess ≠ .owned → ∀ input ∈ captures,
      input.authority.LoanCompatible before witnessAccess input.storage receiver.address
        (if receiverAccess = .shared then .shared else .unique) (receiver.authority.guardLoans before))
    (capturesWitness : witnessAccess ≠ .owned → ∀ input ∈ captures,
      input.authority.LoanCompatible before witnessAccess input.storage witness.address
        (if witnessAccess = .shared then .shared else .unique) (witness.authority.guardLoans before)) :
    ∃ inputs after outcome, PreparesEntryAttempt program callee function before
      (.contextual receiver receiverAccess witness witnessAccess (captures ++ arguments)) inputs after outcome := by
  obtain ⟨value,stored,initialized,head,resources,permission⟩ := callable
  have callable : CallableReceiver program before receiver.address receiver.authority receiverAccess identity instanceArguments :=
    ⟨value,stored,initialized,head,resources,permission⟩
  obtain ⟨witnessValue,witnessId,witnessStored,witnessInitialized,witnessHead,ledger,availableId,active,
    witnessRegion,witnessType,witnessPermission⟩ := witnessReady
  have witnessReady : ContextualWitness before witness witnessAccess available :=
    ⟨witnessValue,witnessId,witnessStored,witnessInitialized,witnessHead,ledger,availableId,active,
      witnessRegion,witnessType,witnessPermission⟩
  rcases Kernel.LendsResident.success_or_exhausted (activation := callee.activation) (scope := callee.scope)
      valid stored initialized resources permission (receiverRequest value stored) with
    ⟨receiverLease,receiverAuthority,middle,receiverLent⟩ | exhausted
  · have middleWell := receiverLent.wellFormed valid
    have middleStored := receiverLent.stores witnessStored (Nat.ne_of_lt (witnessStored.rooted_bound valid)).symm
    have middlePermission := receiverLent.permitted valid witnessPermission witnessCompatible
    have middleResources := receiverLent.resourcesAccessible valid permission
      (witnessResources witnessValue witnessStored) (fun borrowed => witnessViews borrowed witnessValue witnessStored)
    have middleRequest := Kernel.LendsResident.Request.frame valid receiverLent (witnessRequest witnessValue witnessStored)
    have guards := Kernel.StepFrame.guards valid (receiverLent.stepFrame valid) witnessPermission.recorded
    rcases Kernel.LendsResident.success_or_exhausted (activation := callee.activation) (scope := callee.scope)
        middleWell middleStored witnessInitialized middleResources middlePermission middleRequest with
      ⟨witnessLease,witnessAuthority,lent,witnessLent⟩ | exhausted
    · have middleReserved := LendsReceiver.reservationInputs valid receiverLent reserved capturesReceiver
      have lentReserved : ReservationInputs lent available witnessAccess function.captures captures :=
        LendsReceiver.reservationInputs middleWell witnessLent middleReserved (by
          intro borrowed input member
          rw [guards]
          exact Kernel.Authority.LoanCompatible.frame valid (receiverLent.stepFrame valid)
            (reserved.2.2.2 input member).1.recorded (capturesWitness borrowed input member))
      have middleReceiver := receiverLent.stores stored (Nat.ne_of_lt (stored.rooted_bound valid)).symm
      have lentReceiver := witnessLent.stores middleReceiver (Nat.ne_of_lt (middleReceiver.rooted_bound middleWell)).symm
      have receiverPermission := witnessLent.permitted middleWell (receiverLent.borrower_permitted valid permission) (by
        intro borrowed
        rw [guards]
        apply receiverLent.borrowerCompatible (receiverCompatible borrowed)
        intro guard member
        obtain ⟨loan,found,_⟩ := witnessPermission.guardLoans guard member
        exact World.loanBounds valid found)
      obtain ⟨consumed,consumeReceiver⟩ := ConsumesReceiver.exists lentReceiver initialized
        ⟨identity,instanceArguments,head⟩ receiverPermission
      have lentWitness := witnessLent.stores middleStored (Nat.ne_of_lt (middleStored.rooted_bound middleWell)).symm
      have consumedWitness := consumeReceiver.stores_other lentWitness apart
      have consumedLedger : consumed.availability.get witnessId = some available := by
        rw [consumeReceiver.availability,witnessLent.availability,receiverLent.availability]
        exact ledger
      have consumedPermission := (witnessLent.borrower_permitted middleWell middlePermission).locationExtension
        (World.LocationExtension.of_locations consumeReceiver.locations) consumeReceiver.loans
      obtain ⟨after,consumeWitness⟩ := ConsumesAvailability.exists consumedWitness witnessInitialized
        witnessHead consumedLedger active consumedPermission
      exact ⟨_,after,.complete,.contextual callable selected witnessReady reserved receiverLent witnessLent lentReserved
        consumeReceiver (by simpa only [availableId] using consumeWitness)⟩
    · exact ⟨[],middle,.exhausted,.contextualWitnessExhausted callable selected witnessReady reserved receiverLent exhausted⟩
  · exact ⟨[],before,.exhausted,.contextualReceiverExhausted callable selected witnessReady reserved exhausted⟩


/-- The extra preparation obligations are concrete pre-state requests and
compatibility with the existing observed input graph. Recipe identity remains
owned by EntrySource.Ready; no successful preparation or future readiness is
part of this admission. -/
def EntrySource.PreparationConditions (program : Kernel.Program) (world : World) (region : Identity)
    (function : Function) : EntrySource → Prop
  | .supplied _ => True
  | .resident receiver access arguments =>
      CaptureInputs world receiver.address receiver.authority access function.captures
        (ResidentCaptureInputs receiver.address receiver.authority access function.captures) ∧
      (∀ value, world.Stores receiver.address value →
        Kernel.LendsResident.Request program world region receiver.address receiver.authority access value.type) ∧
      (access ≠ .owned → ∀ input ∈ ResidentCaptureInputs receiver.address receiver.authority access function.captures,
        ∀ value, world.Stores input.storage value → value.ViewsLoanCompatible world access receiver.address
          (if access = .shared then .shared else .unique) (receiver.authority.guardLoans world)) ∧
      (access ≠ .owned → ∀ input ∈ arguments, ∀ query requested observed,
        input.ReadsPermission world query requested observed → query.LoanCompatible world requested observed receiver.address
          (if access = .shared then .shared else .unique) (receiver.authority.guardLoans world)) ∧
      (access = .owned → ∀ input ∈ ResidentCaptureInputs receiver.address receiver.authority access function.captures ++ arguments,
        input.formal.IsResident → ¬ input.storage.Prefix receiver.address) ∧
      (access = .owned → ∀ input ∈ ResidentCaptureInputs receiver.address receiver.authority access function.captures ++ arguments,
        ∀ observed, input.RetainsSupport world observed → ¬ observed.Prefix receiver.address)
  | .contextual receiver receiverAccess witness witnessAccess inputs =>
      (¬ receiver.address.Overlaps witness.address) ∧
      (∀ value, world.Stores receiver.address value →
        Kernel.LendsResident.Request program world region receiver.address receiver.authority receiverAccess value.type) ∧
      (∀ value, world.Stores witness.address value →
        Kernel.LendsResident.Request program world region witness.address witness.authority witnessAccess value.type) ∧
      (∀ value, world.Stores witness.address value → value.ResourcesAccessible program world witnessAccess) ∧
      (receiverAccess ≠ .owned → witness.authority.LoanCompatible world witnessAccess witness.address receiver.address
        (if receiverAccess = .shared then .shared else .unique) (receiver.authority.guardLoans world)) ∧
      (witnessAccess ≠ .owned → receiver.authority.LoanCompatible world receiverAccess receiver.address witness.address
        (if witnessAccess = .shared then .shared else .unique) (witness.authority.guardLoans world)) ∧
      (receiverAccess ≠ .owned → ∀ value, world.Stores witness.address value →
        value.ViewsLoanCompatible world witnessAccess receiver.address
          (if receiverAccess = .shared then .shared else .unique) (receiver.authority.guardLoans world)) ∧
      (receiverAccess ≠ .owned → ∀ input ∈ inputs, ∀ query requested observed,
        input.ReadsPermission world query requested observed → query.LoanCompatible world requested observed receiver.address
          (if receiverAccess = .shared then .shared else .unique) (receiver.authority.guardLoans world)) ∧
      (witnessAccess ≠ .owned → ∀ input ∈ inputs, ∀ query requested observed,
        input.ReadsPermission world query requested observed → query.LoanCompatible world requested observed witness.address
          (if witnessAccess = .shared then .shared else .unique) (witness.authority.guardLoans world)) ∧
      (receiverAccess = .owned → ∀ input ∈ inputs, input.formal.IsResident → ¬ input.storage.Prefix receiver.address) ∧
      (receiverAccess = .owned → ∀ input ∈ inputs, ∀ observed, input.RetainsSupport world observed → ¬ observed.Prefix receiver.address) ∧
      (witnessAccess = .owned → ∀ input ∈ inputs, ¬ witness.address.ProperPrefix input.storage) ∧
      (witnessAccess = .owned → ∀ input ∈ inputs, input.formal.IsResident → ¬ witness.address.Overlaps input.storage) ∧
      (witnessAccess = .owned → ∀ input ∈ inputs, ∀ observed, input.RetainsSupport world observed → ¬ witness.address.Overlaps observed)

theorem ReservationInputs.access {world : World} {available : Availability} {access : Access}
    {formals : List Local} {inputs : List InvocationInput}
    (reserved : ReservationInputs world available access formals inputs)
    {input : InvocationInput} (member : input ∈ inputs) : input.access = access := by
  rw [reserved.2.2.1] at member
  obtain ⟨⟨entry,index⟩,_,rfl⟩ := List.mem_map.mp member
  rfl

theorem ReservationInputs.readsPermission {world : World} {available : Availability} {access : Access}
    {formals : List Local} {inputs : List InvocationInput}
    (reserved : ReservationInputs world available access formals inputs)
    {input : InvocationInput} (member : input ∈ inputs) :
    input.ReadsPermission world input.authority input.access input.storage := by
  have permission : Permitted world input.authority input.access input.storage := by
    rw [reserved.access member]
    exact (reserved.2.2.2 input member).1
  refine Or.inl ⟨rfl,rfl,?_,permission⟩
  rw [reserved.2.2.1] at member
  obtain ⟨⟨entry,index⟩,_,rfl⟩ := List.mem_map.mp member
  rfl

/-- Every actual entry recipe has a preparation outcome under its original
physical and alias obligations. The constructed outcome includes owned,
shared, and unique receivers and witnesses, and both ordered exhaustion sites. -/
theorem EntrySource.prepare {program : Kernel.Program} {callee : Context} {function : Function}
    {before : World} {source : EntrySource} (valid : before.WellFormed)
    (ready : source.Ready program before function)
    (conditions : source.PreparationConditions program before callee.region function) :
    ∃ inputs after outcome, PreparesEntryAttempt program callee function before source inputs after outcome := by
  cases source with
  | supplied inputs => exact ⟨inputs,before,.complete,.supplied⟩
  | resident receiver access arguments =>
    obtain ⟨identity,instanceArguments,callable,selected⟩ := ready
    exact PreparesEntryAttempt.resident_progress valid callable selected conditions.1 conditions.2.1
  | contextual receiver receiverAccess witness witnessAccess inputs =>
    obtain ⟨identity,instanceArguments,available,captures,arguments,callable,selected,witnessReady,reserved,rfl,_⟩ := ready
    obtain ⟨apart,receiverRequest,witnessRequest,witnessResources,witnessCompatible,receiverCompatible,
      witnessViews,receiverInputs,witnessInputs,_⟩ := conditions
    apply PreparesEntryAttempt.contextual_progress valid callable selected witnessReady reserved apart
      receiverRequest witnessRequest witnessResources witnessCompatible receiverCompatible witnessViews
    · intro borrowed input member
      have compatible := receiverInputs borrowed input (List.mem_append_left _ member)
        input.authority input.access input.storage (reserved.readsPermission member)
      simpa only [reserved.access member] using compatible
    · intro borrowed input member
      have compatible := witnessInputs borrowed input (List.mem_append_left _ member)
        input.authority input.access input.storage (reserved.readsPermission member)
      simpa only [reserved.access member] using compatible


end Execution


theorem Kernel.StepFrame.of_locations {before after : World} (valid : before.WellFormed)
    (locations : ∀ identity, (after.roots.get identity).map Root.location = (before.roots.get identity).map Root.location)
    (loans : after.loans = before.loans) : StepFrame before after where
  retained := fun _ _ => by rw [loans]
  rooted := fun identity _ => locations identity
  anchored := fun _ _ found _ => by
    obtain ⟨original,selected,_⟩ := World.root_origin locations found
    exact World.root_bound valid selected

/-- A value-only storage effect preserves the whole observed input graph when
its actual read and support frames hold. Permission and custody are derived
from unchanged loan rows and retained physical locations. -/
theorem Kernel.StepObservation.of_storage_frame {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before after : World} {input : InvocationInput}
    (locations : ∀ identity, (after.roots.get identity).map Root.location = (before.roots.get identity).map Root.location)
    (loans : after.loans = before.loans) (nextRoot : before.nextRoot ≤ after.nextRoot)
    (regions : after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion)
    (read : input.formal.IsResident → after.read input.storage = before.read input.storage)
    (located : before.Located input.storage → after.Located input.storage)
    (typed : ∀ type, AddressType program.declarations before input.storage type → AddressType program.declarations after input.storage type)
    (framed : ∀ (localSlot : Local) (value : Value), input.formal = .resident localSlot →
      before.Stores input.storage value → value.SupportFramed before after) :
    StepObservation program footprint region before after input := by
  have extension := World.LocationExtension.of_locations locations
  have permitted : ∀ query requested address, Permitted before query requested address → Permitted after query requested address :=
    fun _ _ _ permission => permission.locationExtension extension loans
  refine ⟨fun resident _ stored => (read resident).trans stored,fun resident _ stored => (read resident).symm.trans stored,nextRoot,located,typed,
    (fun requested _ => permitted _ requested _),AllocationClaim.frame extension loans,
    fun _ loan found => ⟨loan,by rw [loans]; exact found,rfl⟩,
    fun _ loan found => ⟨loan,by rw [loans]; exact found,rfl⟩,
    fun _ _ borrowed => borrowed.transport extension (fun _ loan found => ⟨loan,by rw [loans]; exact found,rfl⟩),
    World.RegionExtension.of_eq regions.1 regions.2,?_,?_⟩
  · intro localSlot value formal stored
    exact ⟨⟨fun _ _ _ _ => by rw [loans],
      fun _ _ _ _ _ _ held => held.frame extension loans⟩,framed localSlot value formal stored⟩
  · exact fun _ _ _ _ query requested address _ permission => permitted query requested address permission

/-- Readiness, physical requests and pairwise interference cross the same
actual observation product; no additional framed-input admission is needed. -/
theorem Kernel.InvocationInputsCompatible.of_observations {program : RuntimeProgram}
    {before after : World} {footprint : List Address} {region : Identity} {inputs : List InvocationInput}
    (valid : before.WellFormed) (afterValid : after.WellFormed) (frame : StepFrame before after)
    (product : InvocationInputsCompatible program footprint region before inputs)
    (observed : ∀ input ∈ inputs, StepObservation program footprint region before after input) :
    InvocationInputsCompatible program footprint region after inputs := by
  have facts := product.inputFramed valid
  have framed : ∀ input ∈ inputs, InputFramed program after input :=
    fun input member => InputFramed.frame (observed input member) (facts input member)
  refine ⟨?_,?_,fun input member => (framed input member).1,?_⟩
  · exact ⟨product.ready.1,product.ready.2.1,fun input member =>
      ⟨InvocationInput.readyFor_of_observation (observed input member) (product.ready.2.2 input member).1,
        (product.ready.2.2 input member).2⟩⟩
  · exact fun input member => InvocationInput.storageRequest_of_observation (observed input member) (product.requests input member)
  · intro head headMember other otherMember different
    exact InvocationInput.IndependentOf.frame valid afterValid frame (observed other otherMember)
      (facts head headMember).1 (facts other otherMember).1 (facts other otherMember).2.1
      (facts other otherMember).2.2 (product.independent headMember otherMember different)


/-- A receiver or witness loan transports the original batch's readiness,
physical requests, provenance and pairwise interference product together.
All loan compatibility is read before the actual lending step. -/
theorem Kernel.LendsResident.inputsCompatible {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {source : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} {footprint : List Address} {inputs : List InvocationInput}
    (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before source authority access lease result after)
    (permission : Permitted before authority access source)
    (product : InvocationInputsCompatible program footprint region before inputs)
    (compatible : access ≠ .owned → ∀ input ∈ inputs, ∀ query requested observed,
      input.ReadsPermission before query requested observed → query.LoanCompatible before requested observed source
        (if access = .shared then .shared else .unique) (authority.guardLoans before)) :
    InvocationInputsCompatible program footprint region after inputs := by
  apply product.of_observations valid (lent.wellFormed valid) (lent.stepFrame valid)
  intro input member
  exact StepObservation.of_lendsResident valid permission lent
    (fun borrowed => compatible borrowed input member) (product.ready.2.2 input member).1
    (product.inputFramed valid input member).2.1


/-- Both contextual loans retain the whole original pending-input product.
The second loan reads its compatibility through the first actual observation;
no middle-world independence or readiness is supplied. -/
theorem Execution.LendsReceiver.contextualInputsCompatible {program : Kernel.Program} {callee : Execution.Context}
    {before middle after : World} {receiver witness : ResolvedPlace} {receiverAccess witnessAccess : Access}
    {receiverLease witnessLease : Option InvocationLease} {receiverAuthority witnessAuthority : Authority}
    {footprint : List Address} {inputs : List InvocationInput} (valid : before.WellFormed)
    (first : Execution.LendsReceiver program callee before receiver.address receiver.authority receiverAccess
      receiverLease receiverAuthority middle)
    (second : Execution.LendsReceiver program callee middle witness.address witness.authority witnessAccess
      witnessLease witnessAuthority after)
    (receiverPermission : Permitted before receiver.authority receiverAccess receiver.address)
    (witnessPermission : Permitted before witness.authority witnessAccess witness.address)
    (product : InvocationInputsCompatible program footprint callee.region before inputs)
    (witnessCompatible : receiverAccess ≠ .owned → witness.authority.LoanCompatible before witnessAccess
      witness.address receiver.address (if receiverAccess = .shared then .shared else .unique) (receiver.authority.guardLoans before))
    (receiverInputs : receiverAccess ≠ .owned → ∀ input ∈ inputs, ∀ query requested observed,
      input.ReadsPermission before query requested observed → query.LoanCompatible before requested observed receiver.address
        (if receiverAccess = .shared then .shared else .unique) (receiver.authority.guardLoans before))
    (witnessInputs : witnessAccess ≠ .owned → ∀ input ∈ inputs, ∀ query requested observed,
      input.ReadsPermission before query requested observed → query.LoanCompatible before requested observed witness.address
        (if witnessAccess = .shared then .shared else .unique) (witness.authority.guardLoans before)) :
    InvocationInputsCompatible program footprint callee.region after inputs := by
  have facts := product.inputFramed valid
  have middleProduct := first.inputsCompatible valid receiverPermission product receiverInputs
  have permission := first.permitted valid witnessPermission witnessCompatible
  have frame := first.stepFrame valid
  have guards := Kernel.StepFrame.guards valid frame witnessPermission.recorded
  apply second.inputsCompatible (first.wellFormed valid) permission middleProduct
  intro borrowed input member query requested observed reads
  have observation := Kernel.StepObservation.of_lendsResident valid receiverPermission first
    (fun borrowed => receiverInputs borrowed input member) (product.ready.2.2 input member).1 (facts input member).2.1
  have recorded : ∀ (localSlot : Local) (value : Value), input.formal = .resident localSlot →
      before.Stores input.storage value → value.ResourcesRecorded before :=
    fun localSlot value formal stored => ((facts input member).2.2 localSlot value formal stored).resourcesRecorded
  have prior := Kernel.InvocationInput.ReadsPermission.backward valid (first.wellFormed valid) frame observation
    (facts input member).1 (facts input member).2.1 reads
  rw [guards]
  exact Kernel.Authority.LoanCompatible.frame valid frame
    (Kernel.InvocationInput.ReadsPermission.recorded (facts input member).1 recorded prior)
    (witnessInputs borrowed input member query requested observed prior)


theorem Execution.ConsumesReceiver.stepObservation {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before after : World} {receiver : Address} {authority : Authority}
    {access : Access} {input : InvocationInput}
    (consumed : Execution.ConsumesReceiver before receiver authority access after)
    (separated : access = .owned → input.formal.IsResident → ¬ input.storage.Prefix receiver)
    (supported : access = .owned → ∀ observed, input.RetainsSupport before observed → ¬ observed.Prefix receiver) :
    StepObservation program footprint region before after input := by
  have state : after.nextRoot = before.nextRoot ∧ after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
    cases consumed with
    | lent => exact ⟨rfl,rfl,rfl⟩
    | owned _ _ _ _ written =>
      have frontier := congrArg World.nextRoot (World.write_rest written)
      exact ⟨frontier,World.write_region_state written⟩
  apply Kernel.StepObservation.of_storage_frame consumed.locations consumed.loans (Nat.le_of_eq state.1.symm) state.2
    (fun resident => consumed.read (fun owned => separated owned resident)) consumed.located (fun _ => consumed.addressType)
  intro localSlot value formal stored observed support
  exact ⟨consumed.read (fun owned => supported owned observed ⟨localSlot,value,formal,stored,support⟩),consumed.locations observed.root⟩

theorem Execution.ConsumesReceiver.inputsCompatible {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before after : World} {receiver : Address} {authority : Authority}
    {access : Access} {inputs : List InvocationInput} (valid : before.WellFormed)
    (consumed : Execution.ConsumesReceiver before receiver authority access after)
    (product : InvocationInputsCompatible program footprint region before inputs)
    (separated : access = .owned → ∀ input ∈ inputs, input.formal.IsResident → ¬ input.storage.Prefix receiver)
    (supported : access = .owned → ∀ input ∈ inputs, ∀ observed,
      input.RetainsSupport before observed → ¬ observed.Prefix receiver) :
    InvocationInputsCompatible program footprint region after inputs :=
  product.of_observations valid (consumed.wellFormed valid)
    (Kernel.StepFrame.of_locations valid consumed.locations consumed.loans)
    (fun input member => consumed.stepObservation (fun owned => separated owned input member)
      (fun owned => supported owned input member))


/-- Lending cannot invent support reachable from an old pending resident.
This is the same actual graph frame used by input readiness, read backwards. -/
theorem Kernel.LendsResident.retainsSupport {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {source observed : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} {footprint : List Address} {input : InvocationInput}
    (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before source authority access lease result after)
    (permission : Permitted before authority access source) (ready : input.ReadyFor program before footprint)
    (supported : input.RetainsSupport after observed) : input.RetainsSupport before observed := by
  obtain ⟨root,found⟩ := ready.root_exists
  have bound := World.root_bound valid (World.root_found found).1
  have read : after.read input.storage = before.read input.storage := by
    unfold World.read World.root
    rw [lent.old_roots bound]
  obtain ⟨localSlot,value,formal,stored,support⟩ := supported
  have originalStored : before.Stores input.storage value := read.symm.trans stored
  have resources := (InvocationInput.ReadyFor.resident ready (by rw [formal]; trivial) originalStored).2.2.1.1
  obtain ⟨batch,framed⟩ := lent.batchFrame valid permission resources
  exact ⟨localSlot,value,formal,originalStored,(Value.Support.frame_batch batch framed).mpr support⟩

/-- Clearing a witness retains erased ports at that exact slot. Only resident
inputs require unchanged contents; physical ports exclude proper descendants,
and reachable resident support excludes the actual cleared storage. -/
theorem Execution.ConsumesAvailability.stepObservation {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before after : World} {witness : Address} {authority : Authority}
    {identity : Identity} {access : Access} {input : InvocationInput}
    (consumed : Execution.ConsumesAvailability before witness authority identity access after)
    (physical : access = .owned → ¬ witness.ProperPrefix input.storage)
    (separated : access = .owned → input.formal.IsResident → ¬ witness.Overlaps input.storage)
    (supported : access = .owned → ∀ observed, input.RetainsSupport before observed → ¬ witness.Overlaps observed) :
    StepObservation program footprint region before after input := by
  cases consumed with
  | lent =>
    apply Kernel.StepObservation.of_storage_frame (fun _ => rfl) rfl (Nat.le_refl _) ⟨rfl,rfl⟩
      (fun _ => rfl) (fun located => located) (fun _ typed => typed)
    exact fun _ _ _ _ _ _ => ⟨rfl,rfl⟩
  | owned stored initialized head ledger active permitted written =>
    rename_i value available cleared
    have frontier := congrArg World.nextRoot (World.write_rest written)
    refine Kernel.StepObservation.of_storage_frame ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact World.write_locations (after := cleared) written
    · exact World.write_loans (after := cleared) written
    · exact Nat.le_of_eq frontier.symm
    · exact World.write_region_state (after := cleared) written
    · exact fun resident => World.write_disjoint (after := cleared) written (separated rfl resident)
    · intro located
      refine World.Located.of_roots (before := cleared) ?_ (World.write_located written (physical rfl) located)
      rfl
    · intro type typed
      refine AddressType.roots_congr (before := cleared) ?_ ((World.write_address_types written (physical rfl)).mp typed)
      rfl
    · intro localSlot value formal stored observed support
      exact ⟨World.write_disjoint (after := cleared) written (supported rfl observed ⟨localSlot,value,formal,stored,support⟩),
        World.write_locations (after := cleared) written observed.root⟩

theorem Execution.ConsumesAvailability.inputsCompatible {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before after : World} {witness : Address} {authority : Authority}
    {identity : Identity} {access : Access} {inputs : List InvocationInput} (valid : before.WellFormed)
    (consumed : Execution.ConsumesAvailability before witness authority identity access after)
    (product : InvocationInputsCompatible program footprint region before inputs)
    (physical : access = .owned → ∀ input ∈ inputs, ¬ witness.ProperPrefix input.storage)
    (separated : access = .owned → ∀ input ∈ inputs, input.formal.IsResident → ¬ witness.Overlaps input.storage)
    (supported : access = .owned → ∀ input ∈ inputs, ∀ observed,
      input.RetainsSupport before observed → ¬ witness.Overlaps observed) :
    InvocationInputsCompatible program footprint region after inputs :=
  product.of_observations valid (consumed.wellFormed valid)
    (Kernel.StepFrame.of_locations valid consumed.locations consumed.loans)
    (fun input member => consumed.stepObservation (fun owned => physical owned input member)
      (fun owned => separated owned input member) (fun owned => supported owned input member))


/-- The complete contextual preparation transports its original input product
through both actual loans, the receiver shell write, and witness clear. Every
compatibility and exclusion premise is read in the original world. -/
theorem Execution.PreparesEntry.contextual_inputsCompatible {program : Kernel.Program} {callee : Execution.Context}
    {function : Function} {before after : World} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {originalInputs inputs : List InvocationInput} {footprint : List Address}
    (valid : before.WellFormed)
    (prepared : Execution.PreparesEntry program callee function before
      (.contextual receiver receiverAccess witness witnessAccess originalInputs) inputs after)
    (product : InvocationInputsCompatible program footprint callee.region before originalInputs)
    (conditions : Execution.EntrySource.PreparationConditions program before callee.region function
      (.contextual receiver receiverAccess witness witnessAccess originalInputs)) :
    InvocationInputsCompatible program footprint callee.region after inputs := by
  cases prepared with
  | contextual callable selected witnessReady original first second reserved consumeReceiver consumeWitness =>
    rename_i captures arguments identity instanceArguments available receiverLease receiverAuthority middle
      witnessLease witnessAuthority lent consumed
    obtain ⟨value,stored,initialized,head,resources,receiverPermission⟩ := callable
    obtain ⟨witnessValue,witnessId,witnessStored,witnessInitialized,witnessHead,ledger,availableId,active,
      liveRegion,witnessType,witnessPermission⟩ := witnessReady
    obtain ⟨apart,receiverRequest,witnessRequest,witnessResources,witnessCompatible,receiverCompatible,
      witnessViews,receiverInputs,witnessInputs,receiverSeparated,receiverSupported,witnessPhysical,witnessSeparated,witnessSupported⟩ := conditions
    have middleWell := first.wellFormed valid
    have lentWell := second.wellFormed middleWell
    have middleProduct := first.inputsCompatible valid receiverPermission product receiverInputs
    have middlePermission := first.permitted valid witnessPermission witnessCompatible
    have lentProduct := Execution.LendsReceiver.contextualInputsCompatible valid first second
      receiverPermission witnessPermission product witnessCompatible receiverInputs witnessInputs
    have supportBefore : ∀ input ∈ captures ++ arguments, ∀ observed,
        input.RetainsSupport lent observed → input.RetainsSupport before observed := by
      intro input member observed support
      exact first.retainsSupport valid receiverPermission (product.ready.2.2 input member).1
        (second.retainsSupport middleWell middlePermission (middleProduct.ready.2.2 input member).1 support)
    have receiverSupport : receiverAccess = .owned → ∀ input ∈ captures ++ arguments, ∀ observed,
        input.RetainsSupport lent observed → ¬ observed.Prefix receiver.address :=
      fun owned input member observed support => receiverSupported owned input member observed (supportBefore input member observed support)
    have consumedProduct := consumeReceiver.inputsCompatible lentWell lentProduct receiverSeparated receiverSupport
    have frame := Kernel.StepFrame.of_locations lentWell consumeReceiver.locations consumeReceiver.loans
    apply consumeWitness.inputsCompatible (consumeReceiver.wellFormed lentWell) consumedProduct witnessPhysical witnessSeparated
    intro owned input member observed support
    have facts := lentProduct.inputFramed lentWell input member
    have observation := consumeReceiver.stepObservation (program := program) (footprint := footprint) (region := callee.region)
      (fun owned => receiverSeparated owned input member) (fun owned => receiverSupport owned input member)
    have prior := Kernel.InvocationInput.RetainsSupport.backward observation support
    exact witnessSupported owned input member observed (supportBefore input member observed prior)


theorem Authority.BorrowRegion.eq_of_same_root {world : World} {authority : Authority}
    {first last : Address} {firstRegion lastRegion : Identity}
    (firstBorrow : authority.BorrowRegion world first firstRegion)
    (lastBorrow : authority.BorrowRegion world last lastRegion) (sameRoot : first.root = last.root) :
    firstRegion = lastRegion := by
  induction authority with
  | owner =>
    obtain ⟨firstRoot,firstFound,firstAt⟩ := firstBorrow
    obtain ⟨lastRoot,lastFound,lastAt⟩ := lastBorrow
    have same := Option.some.inj (firstFound.symm.trans (sameRoot ▸ lastFound))
    exact firstAt.symm.trans ((congrArg Root.region same).trans lastAt)
  | loan identity =>
    obtain ⟨firstLoan,firstFound,firstAt⟩ := firstBorrow
    obtain ⟨lastLoan,lastFound,lastAt⟩ := lastBorrow
    have same := Option.some.inj (firstFound.symm.trans lastFound)
    exact firstAt.symm.trans ((congrArg Loan.region same).trans lastAt)
  | shared backing ih | guarded backing carrier ih => exact ih firstBorrow lastBorrow

/-- A real receiver loan retains the source-region choice of every captured
projection. It does not infer a new lifetime from the temporary handle. -/
theorem Kernel.LendsResident.borrower_region {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {source observed : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} {sourceRegion : Identity}
    (lent : LendsResident program activation scope region before source authority access lease result after)
    (borrowed : authority.BorrowRegion before observed sourceRegion) (sameRoot : observed.root = source.root) :
    result.BorrowRegion after observed sourceRegion := by
  cases lent with
  | owned => exact borrowed
  | lent modes stored original allocated formed =>
    have same := borrowed.eq_of_same_root original sameRoot
    cases formed with
    | borrow _ _ _ _ _ _ _ _ _ _ written =>
      exact ⟨_,Table.get_set _ _ _,same.symm⟩

theorem Kernel.LendsResident.borrower_guards {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {source : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease}
    (lent : LendsResident program activation scope region before source authority access lease result after) :
    result.guardLoans after = authority.guardLoans before := by
  cases lent with
  | owned => rfl
  | lent _ _ _ allocated formed =>
    cases formed with
    | borrow _ _ _ _ _ _ _ _ _ _ written =>
      simpa only [Authority.guardLoans,Table.get_set,Option.map_some,Option.getD_some]
        using Authority.guardLoans.loans_congr allocated.loans authority

/-- A capture changes only its top authority. Its resident graph is framed by
the common actual lender, while top access comes from the new borrower child. -/
theorem Kernel.LendsResident.captureReadyFor {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {receiver : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} {index : Nat} {localSlot : Local} {footprint : List Address}
    (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before receiver authority access lease result after)
    (permission : Permitted before authority access receiver)
    (original : InvocationInput.ReadyFor program before footprint
      ⟨.capture index,.resident localSlot,receiver.child index,authority,access⟩)
    (compatible : access ≠ .owned → ∀ value, before.Stores (receiver.child index) value →
      value.ViewsLoanCompatible before access receiver (if access = .shared then .shared else .unique) (authority.guardLoans before)) :
    InvocationInput.ReadyFor program after footprint
      ⟨.capture index,.resident localSlot,receiver.child index,result,access⟩ := by
  obtain ⟨value,stored,initialized,type,handoff,originalPermission⟩ := original
  obtain ⟨batch,framed⟩ := lent.batchFrame valid permission handoff.1
  refine ⟨value,lent.stores stored (Nat.ne_of_lt (stored.rooted_bound valid)).symm,initialized,type,
    handoff.frame_input batch framed ?_,(lent.borrower_permitted valid permission).child index⟩
  exact fun query requested observed views held =>
    lent.permitted valid held (fun borrowed => compatible borrowed value stored query requested observed views)

/-- The capture's physical request follows its actual re-authored source view;
no prepared-world layout or borrow-region admission is supplied. -/
theorem Kernel.LendsResident.captureStorageRequest {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {receiver : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} {index : Nat} {localSlot : Local}
    (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before receiver authority access lease result after)
    (request : InvocationInput.StorageRequest program before region
      ⟨.capture index,.resident localSlot,receiver.child index,authority,access⟩) :
    InvocationInput.StorageRequest program after region
      ⟨.capture index,.resident localSlot,receiver.child index,result,access⟩ := by
  have rule := lent
  cases lent with
  | owned => exact request
  | lent modes stored original allocated formed =>
    have borrowed : access ≠ .owned := by rcases modes with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp
    simp only [InvocationInput.StorageRequest,if_neg borrowed] at request ⊢
    obtain ⟨sourceRegion,layout,borrowedRegion,sourceType,request⟩ := request
    exact ⟨sourceRegion,layout,rule.borrower_region borrowedRegion rfl,rule.addressType valid sourceType,
      request.same_regions rule.region_state.1 rule.region_state.2⟩


/-- Re-authoring captures preserves the same ordered input product. Captured
resident graphs and unchanged arguments use the actual lender frame; only
capture top authorities change. All alias conditions are original-world reads. -/
theorem Execution.LendsReceiver.residentInputsCompatible {program : Kernel.Program} {callee : Execution.Context}
    {before after : World} {receiver : Address} {authority result : Authority} {access : Access}
    {lease : Option InvocationLease} {formals : List Local} {arguments : List InvocationInput} {footprint : List Address}
    (valid : before.WellFormed)
    (lent : Execution.LendsReceiver program callee before receiver authority access lease result after)
    (permission : Permitted before authority access receiver)
    (product : InvocationInputsCompatible program footprint callee.region before
      (Execution.ResidentCaptureInputs receiver authority access formals ++ arguments))
    (nodup : (Execution.ResidentCaptureInputs receiver authority access formals ++ arguments).Nodup)
    (captureViews : access ≠ .owned → ∀ input ∈ Execution.ResidentCaptureInputs receiver authority access formals,
      ∀ value, before.Stores input.storage value → value.ViewsLoanCompatible before access receiver
        (if access = .shared then .shared else .unique) (authority.guardLoans before))
    (argumentViews : access ≠ .owned → ∀ input ∈ arguments, ∀ query requested observed,
      input.ReadsPermission before query requested observed → query.LoanCompatible before requested observed receiver
        (if access = .shared then .shared else .unique) (authority.guardLoans before)) :
    InvocationInputsCompatible program footprint callee.region after
      (Execution.ResidentCaptureInputs receiver result access formals ++ arguments) := by
  classical
  let captures := Execution.ResidentCaptureInputs receiver authority access formals
  let reauthor (input : InvocationInput) := if input ∈ captures then { input with authority := result } else input
  have argumentApart : ∀ input ∈ arguments, input ∉ captures := by
    intro input member captured
    exact (List.nodup_append.mp nodup).2.2 input captured input member rfl
  have storage : ∀ input, (reauthor input).storage = input.storage := by
    intro input; dsimp only [reauthor]; split <;> rfl
  have formal : ∀ input, (reauthor input).formal = input.formal := by
    intro input; dsimp only [reauthor]; split <;> rfl
  have mode : ∀ input, (reauthor input).access = input.access := by
    intro input; dsimp only [reauthor]; split <;> rfl
  have clears : ∀ input, (reauthor input).clearedStorage = input.clearedStorage := by
    intro input; dsimp only [reauthor]; split <;> rfl
  have capturesMap : captures.map reauthor = Execution.ResidentCaptureInputs receiver result access formals := by
    unfold captures Execution.ResidentCaptureInputs
    rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨localSlot,index⟩ member
    exact if_pos (List.mem_map.mpr ⟨(localSlot,index),member,rfl⟩)
  have argumentsMap : arguments.map reauthor = arguments := by
    calc
      arguments.map reauthor = arguments.map id := List.map_congr_left (fun input member => if_neg (argumentApart input member))
      _ = arguments := List.map_id arguments
  have inputsMap : Execution.ResidentCaptureInputs receiver result access formals ++ arguments =
      (captures ++ arguments).map reauthor := by rw [List.map_append,capturesMap,argumentsMap]
  have facts := product.inputFramed valid
  have afterWell := lent.wellFormed valid
  have frame := lent.stepFrame valid
  have observation : ∀ input ∈ arguments, StepObservation program footprint callee.region before after input := by
    intro input member
    have original := List.mem_append_right captures member
    exact Kernel.StepObservation.of_lendsResident valid permission lent
      (fun borrowed => argumentViews borrowed input member) (product.ready.2.2 input original).1 (facts input original).2.1
  have ready : ∀ input ∈ captures ++ arguments, (reauthor input).ReadyFor program after footprint := by
    intro input member
    by_cases captured : input ∈ captures
    · have original := (product.ready.2.2 input member).1
      have views := fun borrowed value stored => captureViews borrowed input captured value stored
      obtain ⟨⟨localSlot,index⟩,paired,rfl⟩ := List.mem_map.mp captured
      rw [show reauthor _ = ⟨.capture index,.resident localSlot,receiver.child index,result,access⟩ from
        if_pos (List.mem_map.mpr ⟨(localSlot,index),paired,rfl⟩)]
      exact lent.captureReadyFor valid permission original views
    · have argument := (List.mem_append.mp member).resolve_left captured
      rw [show reauthor input = input from if_neg captured]
      exact Kernel.InvocationInput.readyFor_of_observation (observation input argument) (product.ready.2.2 input member).1
  have reads : ∀ input ∈ captures ++ arguments, after.read input.storage = before.read input.storage := by
    intro input member
    unfold World.read World.root
    rw [lent.old_roots (facts input member).2.1]
  have graphs : ∀ input ∈ captures ++ arguments, ∀ localSlot value, input.formal = .resident localSlot →
      before.Stores input.storage value → value.BatchCompatible before after ∧ value.SupportFramed before after :=
    fun input member localSlot value atFormal stored => lent.batchFrame valid permission ((facts input member).2.2 localSlot value atFormal stored)
  rw [inputsMap]
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · simpa only [List.flatMap_map,clears] using product.ready.1
  · simpa only [List.flatMap_map,clears] using product.ready.2.1
  · intro target targetMember
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp targetMember
    refine ⟨ready original member,?_⟩
    simpa only [formal,mode,storage] using (product.ready.2.2 original member).2
  · intro target targetMember
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp targetMember
    by_cases captured : original ∈ captures
    · have request := product.requests original member
      obtain ⟨⟨localSlot,index⟩,paired,rfl⟩ := List.mem_map.mp captured
      rw [show reauthor _ = ⟨.capture index,.resident localSlot,receiver.child index,result,access⟩ from
        if_pos (List.mem_map.mpr ⟨(localSlot,index),paired,rfl⟩)]
      exact lent.captureStorageRequest valid request
    · have argument := (List.mem_append.mp member).resolve_left captured
      rw [show reauthor original = original from if_neg captured]
      exact Kernel.InvocationInput.storageRequest_of_observation (observation original argument) (product.requests original member)
  · intro target targetMember
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp targetMember
    by_cases captured : original ∈ captures
    · rw [show reauthor original = { original with authority := result } from if_pos captured]
      exact (lent.borrower_permitted valid permission).recorded
    · rw [show reauthor original = original from if_neg captured]
      exact (facts original member).1.transport (fun _ loan found => ⟨loan,lent.loan_retained valid found⟩)
  · intro resultHead resultHeadMember resultOther resultOtherMember different
    obtain ⟨head,headMember,rfl⟩ := List.mem_map.mp resultHeadMember
    obtain ⟨other,otherMember,rfl⟩ := List.mem_map.mp resultOtherMember
    have original := product.independent headMember otherMember (fun same => different (congrArg reauthor same))
    have freshRows : ∀ referent rowMode guards kind, (reauthor head).FreshRow after referent rowMode guards kind →
        head.FreshRow before referent rowMode guards kind := by
      intro referent rowMode guards kind fresh
      by_cases captured : head ∈ captures
      · obtain ⟨⟨localSlot,index⟩,paired,rfl⟩ := List.mem_map.mp captured
        rw [show reauthor _ = ⟨.capture index,.resident localSlot,receiver.child index,result,access⟩ from
          if_pos (List.mem_map.mpr ⟨(localSlot,index),paired,rfl⟩)] at fresh
        exact ⟨fresh.1,fresh.2.1,fresh.2.2.1,fresh.2.2.2.1,fresh.2.2.2.2.trans lent.borrower_guards⟩
      · rw [show reauthor head = head from if_neg captured] at fresh
        exact Kernel.InvocationInput.FreshRow.frame valid frame (facts head headMember).1 fresh
    have freshOwning : ∀ parent, (reauthor head).FreshOwning parent → head.FreshOwning parent := by
      intro parent fresh
      by_cases captured : head ∈ captures
      · obtain ⟨⟨localSlot,index⟩,paired,rfl⟩ := List.mem_map.mp captured
        obtain ⟨⟨identity,type,backing,carrier,atFormal,_,_⟩,_⟩ := fresh
        rw [formal] at atFormal
        cases atFormal
      · simpa only [reauthor,if_neg captured] using fresh
    have custodyMoved : ∀ identity, (reauthor head).CustodyMoved after identity → head.CustodyMoved before identity := by
      intro identity moved
      by_cases captured : head ∈ captures
      · obtain ⟨⟨localSlot,index⟩,paired,rfl⟩ := List.mem_map.mp captured
        rcases moved with ⟨obligation,type,atFormal,_⟩ | ⟨obligation,type,atFormal,_⟩ <;>
          rw [formal] at atFormal <;> cases atFormal
      · rw [show reauthor head = head from if_neg captured] at moved
        exact Kernel.InvocationInput.CustodyMoved.frame valid frame (facts head headMember).1 moved
    have residentRecorded : ∀ localSlot value, other.formal = .resident localSlot →
        before.Stores other.storage value → value.ResourcesRecorded before :=
      fun localSlot value atFormal stored => ((facts other otherMember).2.2 localSlot value atFormal stored).resourcesRecorded
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro referent rowMode guards kind fresh query requested observed read
      have beforeFresh := freshRows referent rowMode guards kind fresh
      rcases read with ⟨atAuthority,atAddress,requestedAccess,held⟩ | ⟨localSlot,value,atFormal,stored,views⟩
      · by_cases captured : other ∈ captures
        · have oldReady := (product.ready.2.2 other otherMember).1
          obtain ⟨⟨localSlot,index⟩,paired,rfl⟩ := List.mem_map.mp captured
          have changed : reauthor _ = ⟨.capture index,.resident localSlot,receiver.child index,result,access⟩ :=
            if_pos (List.mem_map.mpr ⟨(localSlot,index),paired,rfl⟩)
          rw [changed] at atAuthority atAddress requestedAccess
          change requested = access at requestedAccess
          subst query; subst observed; subst requested
          obtain ⟨value,stored,initialized,type,handoff,oldPermission⟩ := oldReady
          apply lent.borrowerCompatible (original.permission referent rowMode guards kind beforeFresh
            authority access (receiver.child index) (Or.inl ⟨rfl,rfl,rfl,oldPermission⟩))
          intro identity member
          have guardsEq : guards = head.authority.guardLoans before := by
            cases headFormal : head.formal <;> simp only [InvocationInput.FreshRow,headFormal] at beforeFresh
            · exact beforeFresh.2.2.2.2
            · exact beforeFresh.2.2.2
            · exact beforeFresh.2.2.2.2
          obtain ⟨loan,found⟩ := (facts head headMember).1.guardLoans valid identity (guardsEq ▸ member)
          exact World.loanBounds valid found
        · have argument := (List.mem_append.mp otherMember).resolve_left captured
          have beforeRead := Kernel.InvocationInput.ReadsPermission.backward valid afterWell frame (observation other argument)
            (facts other otherMember).1 (facts other otherMember).2.1
            (by
              rw [show reauthor other = other from if_neg captured] at atAuthority atAddress requestedAccess held
              exact Or.inl ⟨atAuthority,atAddress,requestedAccess,held⟩)
          exact Kernel.Authority.LoanCompatible.frame valid frame
            (Kernel.InvocationInput.ReadsPermission.recorded (facts other otherMember).1 residentRecorded beforeRead)
            (original.permission referent rowMode guards kind beforeFresh query requested observed beforeRead)
      · rw [formal] at atFormal
        rw [storage] at stored
        rw [mode] at views
        have oldStored : before.Stores other.storage value := (reads other otherMember).symm.trans stored
        obtain ⟨batch,framed⟩ := graphs other otherMember localSlot value atFormal oldStored
        have beforeRead : other.ReadsPermission before query requested observed := Or.inr ⟨localSlot,value,atFormal,oldStored,
          Kernel.Value.ObservedViews.backward batch framed views⟩
        exact Kernel.Authority.LoanCompatible.frame valid frame
          (Kernel.InvocationInput.ReadsPermission.recorded (facts other otherMember).1 residentRecorded beforeRead)
          (original.permission referent rowMode guards kind beforeFresh query requested observed beforeRead)
    · intro parent fresh query observed read held anchor atAnchor
      have beforeFresh := freshOwning parent fresh
      have beforeRead : other.ReadsClaim before query observed := by
        rcases read with ⟨atAuthority,atAddress,claim⟩ | ⟨localSlot,value,atFormal,stored,claims⟩
        · by_cases captured : other ∈ captures
          · obtain ⟨⟨localSlot,index⟩,paired,rfl⟩ := List.mem_map.mp captured
            rw [storage] at atAddress
            obtain ⟨_,_,_,_,_,_,_,_,_,whole,_⟩ := claim
            rw [atAddress] at whole
            simp [Address.child] at whole
          · have argument := (List.mem_append.mp otherMember).resolve_left captured
            exact Kernel.InvocationInput.ReadsClaim.backward valid frame (observation other argument)
              (facts other otherMember).1 (facts other otherMember).2.1
              (by
                rw [show reauthor other = other from if_neg captured] at atAuthority atAddress
                exact Or.inl ⟨atAuthority,atAddress,claim⟩)
        · rw [formal] at atFormal
          rw [storage] at stored
          have oldStored : before.Stores other.storage value := (reads other otherMember).symm.trans stored
          obtain ⟨batch,framed⟩ := graphs other otherMember localSlot value atFormal oldStored
          obtain ⟨resident,current,incoming,reached,binding,member,atQuery,atStorage⟩ := claims
          exact Or.inr ⟨localSlot,value,atFormal,oldStored,resident,current,incoming,
            (Value.ReachableResident.frame_batch (authority := .owner) batch framed).mpr reached,
            binding,member,atQuery,atStorage⟩
      have recorded := Kernel.InvocationInput.ReadsClaim.recorded (facts other otherMember).1 residentRecorded beforeRead
      have bound : observed.root < before.nextRoot := by
        obtain ⟨identity,loan,root,domain,atIdentity,found,live,owning,referent,whole,selected,home,latest⟩ := held
        exact frame.anchored observed.root root (World.root_found selected).1
          (home.elim (fun same => Or.inl ⟨domain,same⟩) (fun same => Or.inr ⟨domain,same⟩))
      have oldClaim := AllocationClaim.of_frame valid frame bound (fun identity atIdentity =>
        let ⟨loan,found⟩ := recorded.parentLoan atIdentity; World.loanBounds valid found) held
      obtain ⟨loan,found⟩ := (facts head headMember).1.parentLoan beforeFresh.2
      exact Kernel.StepFrame.claimProtected afterWell frame (World.loanBounds valid found)
        (original.claim parent beforeFresh query observed beforeRead oldClaim anchor atAnchor)
    · intro identity moved query read
      have beforeMoved := custodyMoved identity moved
      rcases read with atAuthority | ⟨localSlot,value,atFormal,stored,custody⟩
      · by_cases captured : other ∈ captures
        · have originalKept := original.custody identity beforeMoved other.authority (Or.inl rfl)
          rw [show reauthor other = { other with authority := result } from if_pos captured] at atAuthority
          subst query
          obtain ⟨⟨localSlot,index⟩,paired,rfl⟩ := List.mem_map.mp captured
          have movedBound : identity < before.nextLoan := by
            have parent : head.authority.parentLoan = some identity := by
              rcases beforeMoved with ⟨obligation,type,atFormal,atLoan⟩ | ⟨obligation,type,atFormal,atLoan,_⟩ <;> rw [atLoan] <;> rfl
            obtain ⟨loan,found⟩ := (facts head headMember).1.parentLoan parent
            exact World.loanBounds valid found
          cases lent with
          | owned => exact originalKept
          | lent _ _ _ allocated _ =>
            intro same
            have equal := Option.some.inj same
            rw [Allocates.nextLoan allocated] at equal
            exact (Nat.ne_of_lt movedBound) equal.symm
        · rw [show reauthor other = other from if_neg captured] at atAuthority
          exact original.custody identity beforeMoved query (Or.inl atAuthority)
      · rw [formal] at atFormal
        rw [storage] at stored
        have oldStored : before.Stores other.storage value := (reads other otherMember).symm.trans stored
        obtain ⟨batch,framed⟩ := graphs other otherMember localSlot value atFormal oldStored
        obtain ⟨resident,current,incoming,reached,binding,member,atQuery⟩ := custody
        exact original.custody identity beforeMoved query (Or.inr ⟨localSlot,value,atFormal,oldStored,resident,current,incoming,
          (Value.ReachableResident.frame_batch (authority := .owner) batch framed).mpr reached,
          binding,member,atQuery⟩)
    · intro address member
      rw [clears] at member
      rw [storage]
      exact original.clear address member
    · intro address retained
      obtain ⟨localSlot,value,atFormal,stored,support⟩ := retained
      have resources := (Kernel.InvocationInput.ReadyFor.resident (ready other otherMember)
        (by rw [atFormal]; trivial) stored).2.2.1.1
      obtain ⟨root,found⟩ := resources.support_root support
      have bound := World.root_bound afterWell (World.root_found found).1
      intro overlap
      exact (Nat.ne_of_lt bound) overlap.1.symm


/-- Resident preparation composes re-authored captures with the actual shell
write. The original coordinate theorem pulls every exclusion back to the
original input product, including support reached through captured values. -/
theorem Execution.PreparesEntry.resident_inputsCompatible {program : Kernel.Program} {callee : Execution.Context}
    {function : Function} {before after : World} {receiver : ResolvedPlace} {access : Access}
    {arguments inputs : List InvocationInput} {footprint : List Address} (valid : before.WellFormed)
    (prepared : Execution.PreparesEntry program callee function before (.resident receiver access arguments) inputs after)
    (product : InvocationInputsCompatible program footprint callee.region before
      (Execution.ResidentCaptureInputs receiver.address receiver.authority access function.captures ++ arguments))
    (nodup : (Execution.ResidentCaptureInputs receiver.address receiver.authority access function.captures ++ arguments).Nodup)
    (conditions : Execution.EntrySource.PreparationConditions program before callee.region function (.resident receiver access arguments)) :
    InvocationInputsCompatible program footprint callee.region after inputs := by
  have originalInput : ∀ input ∈ inputs, ∃ original ∈
      Execution.ResidentCaptureInputs receiver.address receiver.authority access function.captures ++ arguments,
      original.formal = input.formal ∧ original.storage = input.storage := by
    intro input member
    have projected : (input.formal,input.storage) ∈ inputs.map (fun input => (input.formal,input.storage)) :=
      List.mem_map.mpr ⟨input,member,rfl⟩
    rw [prepared.map_inputs (fun input => (input.formal,input.storage)) (by intros; rfl)] at projected
    obtain ⟨original,member,same⟩ := List.mem_map.mp projected
    exact ⟨original,member,Prod.mk.inj same⟩
  cases prepared with
  | resident callable selected lend captures consume =>
    rename_i identity instanceArguments lease result lent captureInputs
    obtain ⟨rfl,captureAccess⟩ := captures
    obtain ⟨value,stored,initialized,head,resources,permission⟩ := callable
    obtain ⟨originalCaptures,request,captureViews,argumentViews,separated,supported⟩ := conditions
    have lentProduct := Execution.LendsReceiver.residentInputsCompatible valid lend permission product nodup captureViews argumentViews
    apply consume.inputsCompatible (lend.wellFormed valid) lentProduct
    · intro owned input member resident
      obtain ⟨original,member,atFormal,atStorage⟩ := originalInput input member
      rw [← atStorage]
      exact separated owned original member (by rw [atFormal]; exact resident)
    · intro owned input member observed support
      obtain ⟨original,member,atFormal,atStorage⟩ := originalInput input member
      obtain ⟨localSlot,value,formal,stored,support⟩ := support
      have oldInputSupport : original.RetainsSupport lent observed :=
        ⟨localSlot,value,atFormal.trans formal,by rw [atStorage]; exact stored,support⟩
      exact supported owned original member observed
        (lend.retainsSupport valid permission (product.ready.2.2 original member).1 oldInputSupport)

/-- Every successful actual source recipe obtains its prepared input product
from the original one. Preparation never admits its own successor readiness. -/
theorem Execution.PreparesEntry.inputsCompatible {program : Kernel.Program} {callee : Execution.Context}
    {function : Function} {before after : World} {source : Execution.EntrySource}
    {inputs : List InvocationInput} {footprint : List Address} (valid : before.WellFormed)
    (prepared : Execution.PreparesEntry program callee function before source inputs after)
    (product : InvocationInputsCompatible program footprint callee.region before (source.originalInputs function))
    (nodup : (source.originalInputs function).Nodup)
    (conditions : source.PreparationConditions program before callee.region function) :
    InvocationInputsCompatible program footprint callee.region after inputs := by
  cases source with
  | supplied original => cases prepared; exact product
  | resident receiver access arguments => exact prepared.resident_inputsCompatible valid product nodup conditions
  | contextual receiver receiverAccess witness witnessAccess original =>
    exact prepared.contextual_inputsCompatible valid product conditions

/-- Constructive preparation and original-input transport share the same
preflight contract and actual attempt. Physical failure retains its exact
prefix; completion publishes the whole input product consumed by binding. -/
theorem Execution.EntrySource.prepareInputs {program : Kernel.Program} {callee : Execution.Context} {function : Function}
    {before : World} {source : Execution.EntrySource} {footprint : List Address} (valid : before.WellFormed)
    (ready : source.Ready program before function)
    (conditions : source.PreparationConditions program before callee.region function)
    (product : InvocationInputsCompatible program footprint callee.region before (source.originalInputs function))
    (nodup : (source.originalInputs function).Nodup) :
    ∃ inputs after outcome, Execution.PreparesEntryAttempt program callee function before source inputs after outcome ∧
      (outcome = .complete → InvocationInputsCompatible program footprint callee.region after inputs) := by
  obtain ⟨inputs,after,outcome,prepared⟩ := source.prepare valid ready conditions
  refine ⟨inputs,after,outcome,prepared,?_⟩
  intro complete
  subst outcome
  exact Execution.PreparesEntry.inputsCompatible valid prepared product nodup conditions


/-- A fresh lifetime preserves the same authoritative input observations.
Only lifetime metadata grows; no input storage, authority or loan row changes. -/
theorem FreshRegion.stepObservation {program : RuntimeProgram} {before after : World}
    {freshRegion region : Identity} {footprint : List Address} {input : InvocationInput}
    (fresh : FreshRegion before freshRegion after) : StepObservation program footprint region before after input := by
  have roots : after.roots = before.roots := by rw [fresh.2]
  have loans : after.loans = before.loans := by rw [fresh.2]
  have extension := World.LocationExtension.of_roots roots
  apply Kernel.StepObservation.of_loans roots (by rw [fresh.2]; exact Nat.le_refl _) fresh.regionExtension
    (fun _ loan found => ⟨loan,by rw [loans]; exact found,rfl⟩)
    (fun _ loan found => ⟨loan,by rw [loans]; exact found,rfl⟩)
  · exact fun _ _ _ _ permission => permission.locationExtension extension loans
  · exact fun _ _ _ claim => claim.frame extension loans
  · exact fun _ _ _ _ => Value.BatchCompatible.of_eq extension loans
  · exact fun _ _ _ _ => Value.SupportFramed.of_roots roots
  · exact fun _ _ _ _ _ _ _ _ permission => permission.locationExtension extension loans

theorem Kernel.InvocationInput.StorageRequest.retarget {program : RuntimeProgram} {world : World}
    {original target : Identity} {input : InvocationInput}
    (request : input.StorageRequest program world original) (live : target ∈ world.liveRegions) :
    input.StorageRequest program world target := by
  cases formal : input.formal with
  | resident localSlot =>
    simp only [InvocationInput.StorageRequest,formal] at request ⊢
    by_cases owned : input.access = .owned
    · simp only [if_pos owned] at request ⊢
      obtain ⟨layout,request⟩ := request
      exact ⟨layout,request.retarget live (Nat.le_refl _)⟩
    · simp only [if_neg owned] at request ⊢
      obtain ⟨region,layout,borrowed,typed,request⟩ := request
      exact ⟨region,layout,borrowed,typed,request.retarget live (Nat.le_refl _)⟩
  | storage _ _ | allocation _ _ | loan _ _ => simp only [InvocationInput.StorageRequest,formal]

theorem Kernel.InvocationInputsCompatible.retarget {program : RuntimeProgram} {world : World}
    {original target : Identity} {footprint : List Address} {inputs : List InvocationInput}
    (product : InvocationInputsCompatible program footprint original world inputs) (live : target ∈ world.liveRegions) :
    InvocationInputsCompatible program footprint target world inputs :=
  ⟨product.1,fun input member => (product.requests input member).retarget live,product.2.2⟩

/-- Caller-world requests select the same layouts for the new callee lifetime.
The whole readiness/interference product crosses the actual fresh-region step;
it is not re-admitted in the resulting world. -/
theorem FreshRegion.inputsCompatible {program : RuntimeProgram} {before after : World}
    {original region : Identity} {footprint : List Address} {inputs : List InvocationInput}
    (valid : before.WellFormed) (fresh : FreshRegion before region after)
    (product : InvocationInputsCompatible program footprint original before inputs) :
    InvocationInputsCompatible program footprint region after inputs := by
  have roots : after.roots = before.roots := by rw [fresh.2]
  have loans : after.loans = before.loans := by rw [fresh.2]
  have framed := product.of_observations valid (fresh.wellFormed valid)
    (Kernel.StepFrame.of_locations valid (fun _ => by rw [roots]) loans) (fun _ _ => fresh.stepObservation)
  exact framed.retarget (by rw [fresh.2]; exact List.mem_cons_self)

/-- The same positive receiver/witness request is retargeted before preparation;
its referent's source lifetime remains unchanged. -/
theorem Kernel.LendsResident.Request.freshRegion {program : RuntimeProgram} {before after : World}
    {original region : Identity} {address : Address} {authority : Authority} {access : Access} {type : Term}
    (fresh : FreshRegion before region after) (request : LendsResident.Request program before original address authority access type) :
    LendsResident.Request program after region address authority access type := by
  intro borrowed
  obtain ⟨sourceRegion,layout,source,typed,request⟩ := request borrowed
  have roots : after.roots = before.roots := by rw [fresh.2]
  have loans : after.loans = before.loans := by rw [fresh.2]
  exact ⟨sourceRegion,layout,source.transport (World.LocationExtension.of_roots roots)
    (fun _ loan found => ⟨loan,by rw [loans]; exact found,rfl⟩),AddressType.roots_congr roots typed,
    request.retarget (by rw [fresh.2]; exact List.mem_cons_self) fresh.regionExtension.frontier⟩


theorem FreshRegion.resourcesAccessible {program : RuntimeProgram} {before after : World} {region : Identity}
    {value : Value} {access : Access} (fresh : FreshRegion before region after)
    (resources : value.ResourcesAccessible program before access) : value.ResourcesAccessible program after access := by
  have roots : after.roots = before.roots := by rw [fresh.2]
  have loans : after.loans = before.loans := by rw [fresh.2]
  have extension := World.LocationExtension.of_roots roots
  exact resources.frame extension loans (Value.SupportFramed.of_roots roots)

theorem FreshRegion.viewsLoanCompatible {before after : World} {region : Identity} {value : Value}
    {access : Access} {referent : Address} {mode : Mutability} {guards : List Identity}
    (fresh : FreshRegion before region after)
    (compatible : value.ViewsLoanCompatible before access referent mode guards) :
    value.ViewsLoanCompatible after access referent mode guards := by
  have roots : after.roots = before.roots := by rw [fresh.2]
  have loans : after.loans = before.loans := by rw [fresh.2]
  have extension := World.LocationExtension.of_roots roots
  intro query requested observed views
  exact Authority.LoanCompatible.loans_congr loans (compatible query requested observed
    (Kernel.Value.ObservedViews.backward (Value.BatchCompatible.of_eq extension loans)
      (Value.SupportFramed.of_roots roots) views))

/-- Fresh-region creation retains the actual recipe, including whole receivers
and contextual witnesses independently of their capture counts. -/
theorem FreshRegion.entrySourceReady {program : Kernel.Program} {before after : World} {region : Identity}
    {function : Function} {source : Execution.EntrySource}
    (fresh : FreshRegion before region after) (ready : source.Ready program before function) :
    source.Ready program after function := by
  have roots : after.roots = before.roots := by rw [fresh.2]
  have loans : after.loans = before.loans := by rw [fresh.2]
  have availability : after.availability = before.availability := by rw [fresh.2]
  have extension := World.LocationExtension.of_roots roots
  have callable : ∀ address authority access identity arguments,
      Execution.CallableReceiver program before address authority access identity arguments →
      Execution.CallableReceiver program after address authority access identity arguments := by
    intro address authority access identity arguments original
    obtain ⟨value,stored,initialized,head,resources,permission⟩ := original
    exact ⟨value,World.Stores.of_roots roots stored,initialized,head,fresh.resourcesAccessible resources,
      permission.locationExtension extension loans⟩
  cases source with
  | supplied => trivial
  | resident receiver access arguments =>
    obtain ⟨identity,instanceArguments,original,selected⟩ := ready
    exact ⟨identity,instanceArguments,callable _ _ _ _ _ original,selected⟩
  | contextual receiver receiverAccess witness witnessAccess inputs =>
    obtain ⟨identity,instanceArguments,available,captures,arguments,original,selected,witnessReady,reserved,atInputs,
      shell,storedShell,empty⟩ := ready
    refine ⟨identity,instanceArguments,available,captures,arguments,callable _ _ _ _ _ original,selected,?_,?_,
      atInputs,shell,World.Stores.of_roots roots storedShell,empty⟩
    · obtain ⟨value,id,stored,initialized,head,ledger,availableId,active,live,type,permission⟩ := witnessReady
      exact ⟨value,id,World.Stores.of_roots roots stored,initialized,head,by rw [availability]; exact ledger,
        availableId,active,fresh.regionExtension.regions _ live,type,permission.locationExtension extension loans⟩
    · refine ⟨reserved.1,reserved.2.1,reserved.2.2.1,?_⟩
      intro input member
      obtain ⟨permission,value,stored,initialized,type⟩ := reserved.2.2.2 input member
      exact ⟨permission.locationExtension extension loans,value,World.Stores.of_roots roots stored,initialized,type⟩


/-- The source preflight crosses actual fresh-lifetime creation. Requests are
retargeted; all graph compatibility and write exclusions are reflected to the
caller-world input product before they are used. -/
theorem FreshRegion.entryPreparationConditions {program : Kernel.Program} {before after : World}
    {original region : Identity} {function : Function} {source : Execution.EntrySource} {footprint : List Address}
    (valid : before.WellFormed) (fresh : FreshRegion before region after)
    (product : InvocationInputsCompatible program footprint original before (source.originalInputs function))
    (conditions : source.PreparationConditions program before original function) :
    source.PreparationConditions program after region function := by
  have roots : after.roots = before.roots := by rw [fresh.2]
  have loans : after.loans = before.loans := by rw [fresh.2]
  have extension := World.LocationExtension.of_roots roots
  have frame := Kernel.StepFrame.of_locations valid (fun _ => by rw [roots]) loans
  have facts := product.inputFramed valid
  have stores : ∀ address value, after.Stores address value → before.Stores address value :=
    fun _ _ => World.Stores.of_roots roots.symm
  have guards : ∀ authority : Authority, authority.guardLoans after = authority.guardLoans before :=
    Authority.guardLoans.loans_congr loans
  have reads : ∀ input ∈ source.originalInputs function, ∀ query requested observed,
      input.ReadsPermission after query requested observed → input.ReadsPermission before query requested observed := by
    intro input member query requested observed read
    exact Kernel.InvocationInput.ReadsPermission.backward valid (fresh.wellFormed valid) frame
      (fresh.stepObservation (program := program) (footprint := footprint) (region := original))
      (facts input member).1 (facts input member).2.1
      read
  have support : ∀ input ∈ source.originalInputs function, ∀ observed,
      input.RetainsSupport after observed → input.RetainsSupport before observed := by
    intro input member observed retained
    exact Kernel.InvocationInput.RetainsSupport.backward
      (fresh.stepObservation (program := program) (footprint := footprint) (region := original)) retained
  cases source with
  | supplied => trivial
  | resident receiver access arguments =>
    obtain ⟨captures,request,captureViews,argumentViews,separated,supported⟩ := conditions
    refine ⟨⟨captures.1,?_⟩,?_,?_,?_,separated,?_⟩
    · intro input member
      obtain ⟨⟨value,stored,initialized⟩,permission⟩ := captures.2 input member
      exact ⟨⟨value,World.Stores.of_roots roots stored,initialized⟩,permission.locationExtension extension loans⟩
    · exact fun value stored => (request value (stores _ _ stored)).freshRegion fresh
    · intro borrowed input member value stored
      have prior := stores _ _ stored
      have compatible := captureViews borrowed input member value prior
      rw [guards]
      exact fresh.viewsLoanCompatible compatible
    · intro borrowed input member query requested observed read
      rw [guards]
      exact Authority.LoanCompatible.loans_congr loans
        (argumentViews borrowed input member query requested observed (reads input (List.mem_append_right _ member) _ _ _ read))
    · exact fun owned input member observed retained => supported owned input member observed (support input member observed retained)
  | contextual receiver receiverAccess witness witnessAccess inputs =>
    obtain ⟨apart,receiverRequest,witnessRequest,witnessResources,witnessCompatible,receiverCompatible,
      witnessViews,receiverInputs,witnessInputs,receiverSeparated,receiverSupported,witnessPhysical,witnessSeparated,witnessSupported⟩ := conditions
    refine ⟨apart,?_,?_,?_,?_,?_,?_,?_,?_,receiverSeparated,?_,witnessPhysical,witnessSeparated,?_⟩
    · exact fun value stored => (receiverRequest value (stores _ _ stored)).freshRegion fresh
    · exact fun value stored => (witnessRequest value (stores _ _ stored)).freshRegion fresh
    · exact fun value stored => fresh.resourcesAccessible (witnessResources value (stores _ _ stored))
    · intro borrowed
      rw [guards]
      exact Authority.LoanCompatible.loans_congr loans (witnessCompatible borrowed)
    · intro borrowed
      rw [guards]
      exact Authority.LoanCompatible.loans_congr loans (receiverCompatible borrowed)
    · intro borrowed value stored
      have prior := stores _ _ stored
      rw [guards]
      exact fresh.viewsLoanCompatible (witnessViews borrowed value prior)
    · intro borrowed input member query requested observed read
      rw [guards]
      exact Authority.LoanCompatible.loans_congr loans
        (receiverInputs borrowed input member query requested observed (reads input member _ _ _ read))
    · intro borrowed input member query requested observed read
      rw [guards]
      exact Authority.LoanCompatible.loans_congr loans
        (witnessInputs borrowed input member query requested observed (reads input member _ _ _ read))
    · exact fun owned input member observed retained => receiverSupported owned input member observed (support input member observed retained)
    · exact fun owned input member observed retained => witnessSupported owned input member observed (support input member observed retained)

/-- Construct the real fresh lifetime and the entire preparation outcome from
the caller-world recipe, input product and positive requests. No fresh-world
readiness or chosen preparation derivation is an admission premise. -/
theorem Execution.EntrySource.prepareFreshInputs {program : Kernel.Program} {callee : Execution.Context}
    {function : Function} {before : World} {source : Execution.EntrySource}
    {original : Identity} {footprint : List Address} (valid : before.WellFormed)
    (calleeRegion : callee.region = before.nextRegion)
    (ready : source.Ready program before function)
    (conditions : source.PreparationConditions program before original function)
    (product : InvocationInputsCompatible program footprint original before (source.originalInputs function))
    (incoming : IncomingResources program function before (source.originalInputs function)) :
    ∃ withRegion inputs after outcome,
      FreshRegion before callee.region withRegion ∧
      Execution.PreparesEntryAttempt program callee function withRegion source inputs after outcome ∧
      (outcome = .complete → InvocationInputsCompatible program footprint callee.region after inputs) := by
  let withRegion := { before with liveRegions := before.nextRegion :: before.liveRegions, nextRegion := before.nextRegion+1 }
  have fresh : FreshRegion before callee.region withRegion := ⟨calleeRegion,by rw [calleeRegion]⟩
  have nodup : (source.originalInputs function).Nodup := (List.pairwise_map.mp incoming.1).imp
    (fun different same => different (congrArg (fun input => input.formal.key) same))
  obtain ⟨inputs,after,outcome,prepared,product⟩ := source.prepareInputs (fresh.wellFormed valid)
    (fresh.entrySourceReady ready) (fresh.entryPreparationConditions valid product conditions)
    (fresh.inputsCompatible valid product) nodup
  exact ⟨withRegion,inputs,after,outcome,fresh,prepared,product⟩


/-- Value-only writes after a lending step preserve that same physical and
loan-row frame. They neither create a second fresh row nor move a root. -/
theorem Kernel.StepFrame.follow_locations {before middle after : World} (frame : StepFrame before middle)
    (locations : ∀ identity, (after.roots.get identity).map Root.location = (middle.roots.get identity).map Root.location)
    (loans : after.loans = middle.loans) : StepFrame before after where
  retained := fun identity different => by rw [loans]; exact frame.retained identity different
  rooted := fun identity bounded => (locations identity).trans (frame.rooted identity bounded)
  anchored := fun identity root found home => by
    obtain ⟨original,selected,same⟩ := World.root_origin locations found
    exact frame.anchored identity original selected (by simpa only [congrArg Root.home same] using home)

/-- Owned preparation keeps the original input authorities. Its only possible
fresh row is the contextual witness loan; actual shell/witness consumption
preserves the resulting frame. The receiver's record comes from its actual
callable permission, not a separate provenance admission. -/
theorem Execution.PreparesEntry.ownedReceiver_frame {program : Kernel.Program} {callee : Execution.Context}
    {function : Function} {before after : World} {source : Execution.EntrySource} {inputs : List InvocationInput}
    {receiver : ResolvedPlace} (valid : before.WellFormed)
    (prepared : Execution.PreparesEntry program callee function before source inputs after)
    (owned : source.ownedReceiver = some receiver) :
    inputs = source.originalInputs function ∧ StepFrame before after ∧ receiver.authority.Recorded before.loans := by
  cases prepared with
  | supplied => cases owned
  | resident callable _ lent captures consumed =>
    simp only [Execution.EntrySource.ownedReceiver] at owned
    split at owned
    next mode =>
      cases mode
      cases Option.some.inj owned
      cases lent with
      | owned =>
        obtain ⟨value,stored,initialized,head,resources,permission⟩ := callable
        exact ⟨by simp only [Execution.EntrySource.originalInputs,captures.1],
          Kernel.StepFrame.of_locations valid consumed.locations consumed.loans,permission.recorded⟩
      | lent modes _ _ _ _ => simp at modes
    next => cases owned
  | contextual callable _ _ _ receiverLent witnessLent _ consumed cleared =>
    simp only [Execution.EntrySource.ownedReceiver] at owned
    split at owned
    next mode =>
      cases mode
      cases Option.some.inj owned
      cases receiverLent with
      | owned =>
        obtain ⟨value,stored,initialized,head,resources,permission⟩ := callable
        exact ⟨rfl,((witnessLent.stepFrame valid).follow_locations consumed.locations consumed.loans).follow_locations
          cleared.locations cleared.loans,permission.recorded⟩
      | lent modes _ _ _ _ => simp at modes
    next => cases owned

/-- The owned receiver's compatibility is checked against original inputs in
the caller world. Actual fresh-region and preparation frames derive the binder
premise; no compatibility predicate at the prepared world is assumed. -/
theorem Execution.PreparesEntry.original_receiver_compatible {program : Kernel.Program} {callee : Execution.Context}
    {function : Function} {original before after : World} {source : Execution.EntrySource} {inputs : List InvocationInput}
    {region : Identity} (valid : original.WellFormed) (fresh : FreshRegion original region before)
    (prepared : Execution.PreparesEntry program callee function before source inputs after)
    (recorded : ∀ input ∈ source.originalInputs function, input.authority.Recorded original.loans)
    (compatible : ∀ receiver, source.ownedReceiver = some receiver → ∀ input ∈ source.originalInputs function,
      input.PermissionCompatible original receiver.authority .owned receiver.address) :
    ∀ receiver, source.ownedReceiver = some receiver → ∀ input ∈ inputs,
      input.PermissionCompatible after receiver.authority .owned receiver.address := by
  intro receiver owned input member
  obtain ⟨same,frame,receiverRecorded⟩ := prepared.ownedReceiver_frame (fresh.wellFormed valid) owned
  rw [same] at member
  have originalFrame : StepFrame original after := by
    obtain ⟨rfl,rfl⟩ := fresh
    exact ⟨frame.retained,frame.rooted,frame.anchored⟩
  have originalRecorded : receiver.authority.Recorded original.loans := by
    simpa only [fresh.2] using receiverRecorded
  exact (compatible receiver owned input member).frame valid originalFrame (recorded input member) originalRecorded


/-- Original-world entry obligations, before creating the callee lifetime.
These are source/storage/loan/layout predicates, not execution, progress or
future-world finishing assumptions. Proper-tail caller cleanup is separate. -/
structure Execution.EntrySource.Admitted (program : Kernel.Program) (world : World) (region : Identity)
    (function : Function) (source : Execution.EntrySource) : Prop where
  ready : source.Ready program world function
  preparation : source.PreparationConditions program world region function
  inputs : InvocationInputsCompatible program ((source.originalInputs function).flatMap InvocationInput.clearedStorage)
    region world (source.originalInputs function)
  incoming : IncomingResources program function world (source.originalInputs function)
  receiverCompatible : ∀ receiver, source.ownedReceiver = some receiver → ∀ input ∈ source.originalInputs function,
    input.PermissionCompatible world receiver.authority .owned receiver.address


/-- Whole entry from original invocation facts: create the callee lifetime,
prepare the actual recipe, bind every resident/raw input in order and retire
an owned receiver. Either physical exhaustion preserves its real prefix, or
all phases complete. No intermediate-world admission or finishing callback
is a premise. -/
theorem Execution.EntrySource.Admitted.enterWorldAttempt {program : Kernel.Program} {before : Execution.State}
    {caller : Execution.Context} {function : Function} {source : Execution.EntrySource}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (admitted : source.Admitted program before.world caller.region function)
    (declared : ∃ declaration, program.declarations.function function.declaration = some declaration)
    (callerUnsafe : function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) :
    ∃ context after outcome, Execution.EnterWorldAttempt program before caller function source context after outcome := by
  obtain ⟨ready,conditions,product,incoming,receiverCompatible⟩ := admitted
  obtain ⟨declaration,declared⟩ := declared
  let callee : Execution.Context := ⟨[],declaration.header.module,before.nextActivation,before.world.nextRegion,
    before.world.nextRegion,function.entryScope before.world.nextRegion before.nextBrand,false,[⟨function.declaration,[]⟩]⟩
  obtain ⟨withRegion,inputs,after,outcome,fresh,prepared,preparedInputs⟩ :=
    source.prepareFreshInputs (callee := callee) typed.1 rfl ready conditions product incoming
  cases outcome with
  | complete =>
    have footprint : inputs.flatMap InvocationInput.clearedStorage =
        (source.originalInputs function).flatMap InvocationInput.clearedStorage :=
      congrArg List.flatten (Execution.PreparesEntry.map_inputs prepared InvocationInput.clearedStorage (by intros; rfl))
    have inputsReady : InvocationInputsCompatible program (inputs.flatMap InvocationInput.clearedStorage)
        before.world.nextRegion after inputs := by
      rw [footprint]
      exact preparedInputs rfl
    exact Kernel.EntryBatch.enterWorldAttempt callee ⟨rfl,rfl,rfl⟩ valid inventory typed ready
      ⟨declaration,declared⟩ prepared fresh incoming inputsReady
      (Execution.PreparesEntry.original_receiver_compatible typed.1 fresh prepared
        (fun input member => product.2.2.1 input member) receiverCompatible)
      callerUnsafe
  | exhausted =>
    have empty := prepared.exhausted_inputs
    subst inputs
    exact ⟨callee,after,.exhausted,.preparationExhausted declared fresh prepared incoming rfl callerUnsafe⟩


/-- The original admission is consumed by the actual non-tail machine step,
including physical resource failure. It does not merely produce a prepared
world or an unused compatibility certificate. -/
theorem Execution.EntrySource.Admitted.enterStep {program : Kernel.Program} {before : Execution.State}
    {caller : Execution.Context} {function : Function} {source : Execution.EntrySource}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (admitted : source.Admitted program before.world caller.region function)
    (declared : ∃ declaration, program.declarations.function function.declaration = some declaration)
    (task : before.task = .enter caller function source false)
    (callerUnsafe : function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) :
    ∃ event after, Execution.LocalStep program before event after := by
  obtain ⟨context,world,outcome,entered⟩ := admitted.enterWorldAttempt valid inventory typed declared callerUnsafe
  cases outcome with
  | complete => exact ⟨none,_,.enter task entered⟩
  | exhausted => exact ⟨some (.fatal .resource),_,.enterExhausted task entered⟩


end Glorious.Language

