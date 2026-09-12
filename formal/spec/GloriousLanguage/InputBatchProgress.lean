import GloriousLanguage.InputBindingProgress
import GloriousLanguage.HandoffPreservation
import GloriousLanguage.ReferenceTransferPreservation
import GloriousLanguage.LoanCompatibility
import GloriousLanguage.LoanResourceRows
import GloriousLanguage.BindingPersistence
import GloriousLanguage.ResidentMutationPreservation

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
      authority = current.referenceView world identity (ReferenceAccess viewAccess loan.mode) ∧
      requested = ReferenceAccess viewAccess loan.mode ∧ address = loan.referent) ∨
  (∃ resident current incoming binding,
      value.ReachableResident world .owner access resident current incoming ∧
      binding ∈ resident.resources ∧
      authority = current.resourceView world binding incoming ∧
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

/-- A permission the pending input's own readiness actually reads: its own
authority view, and, for a resident, the whole reachable graph of the value
stored at its storage. -/
def InvocationInput.ReadsPermission (world : World) (input : InvocationInput)
    (authority : Authority) (access : Access) (address : Address) : Prop :=
  (authority = input.authority ∧ address = input.storage ∧
    ((access = input.access ∧ Permitted world input.authority input.access input.storage) ∨
      ((∃ identity type, input.formal = .allocation identity type) ∧ access = Access.owned ∧
        Permitted world input.authority Access.owned input.storage))) ∨
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
    (valid : before.WellFormed) (resources : value.ResourcesRecorded before)
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : value.FramePermitted before after access)
    (ready : value.ReferencesAccessible before .owner access) :
    value.ReferencesAccessible after .owner access := by
  intro identity current access reached
  have prior := (Value.ReachableReference.frame_batch (authority := .owner) valid resources trivial batch
    framed).mpr reached
  have guardFrame : current.guardLoans after = current.guardLoans before := by
    obtain ⟨resident,priorReach,head⟩ := prior
    exact (priorReach.recorded (authority := .owner) valid resources trivial).guards_framed batch.guards
  obtain ⟨loan,found,live,permission⟩ := ready identity current access prior
  obtain ⟨changed,selected,shape⟩ := batch.rows.selected prior found
  obtain ⟨_,_,referent,mode,_,active,_,_⟩ := Loan.permissionState_eq_iff.mp shape
  refine ⟨changed,selected,active.trans live,?_⟩
  have stated := permitted (current.referenceView before identity (ReferenceAccess access loan.mode))
    (ReferenceAccess access loan.mode) loan.referent
    (Or.inl ⟨identity,current,access,loan,prior,found,rfl,rfl,rfl⟩) permission
  simpa only [referent,mode,Authority.referenceView_of_guardLoans guardFrame] using stated

theorem Value.ResourcesAccessible.frame_input {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access}
    (valid : before.WellFormed)
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : value.FramePermitted before after access)
    (ready : value.ResourcesAccessible program before access) :
    value.ResourcesAccessible program after access := by
  have resources := ready.resourcesRecorded
  refine ⟨ready.1.frame_batch valid resources batch framed,
    ready.2.1.frame_batch valid resources batch framed,
    ready.references.frame_input valid resources batch framed permitted,?_⟩
  intro resident authority incoming reached binding member
  have prior := (Value.ReachableResident.frame_batch (authority := .owner) valid resources trivial batch
    framed).mpr reached
  have permission := ready.2.2.2 resident authority incoming prior binding member
  have recorded := prior.recorded (authority := .owner) valid resources trivial
  have stated := permitted (authority.resourceView before binding incoming)
    (ResourceAccess incoming binding) binding.address
    (Or.inr ⟨resident,authority,incoming,binding,prior,member,rfl,rfl,rfl⟩) permission
  simpa only [Authority.resourceView_of_guardLoans (recorded.guards_framed batch.guards)] using stated

theorem Value.HandoffReady.frame_input {program : RuntimeProgram} {before after : World}
    {value : Value} {access : Access} {footprint : List Address}
    (valid : before.WellFormed)
    (batch : value.BatchCompatible before after) (framed : value.SupportFramed before after)
    (permitted : value.FramePermitted before after access)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint :=
  ⟨ready.1.frame_input valid batch framed permitted,
    fun source member observed supported =>
      ready.2 source member observed
        ((Value.Support.frame_batch valid ready.1.resourcesRecorded batch framed).mpr supported)⟩

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

theorem World.RecordedGuardsFramed.of_fresh_loan {before after : World} {fresh : Loan}
    (valid : before.WellFormed)
    (loans : after.loans = before.loans.set before.nextLoan fresh) :
    before.RecordedGuardsFramed after := by
  intro identity loan found
  rw [loans,Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid found)),found]
  rfl

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
   World.RecordedGuardsFramed.of_fresh_loan valid loans,
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
   (fun _ _ found => by rw [loans,found]; rfl),
   (fun resident authority access reached binding member held => held.frame locations loans)⟩

namespace Kernel

/-- Everything an actual binding step is observed to do by one other input of
the same batch: which of that input's world facts survive, and how its own
retained value graph is framed. -/
structure StepObservation (program : RuntimeProgram) (footprint : List Address) (region : Identity)
    (before middle : World) (other : InvocationInput) : Prop where
  stores : ∀ value, before.Stores other.storage value → middle.Stores other.storage value
  /-- The write side of the same observation: the step never installs storage
  at the other input's address that the source world did not already hold. -/
  storesBack : ∀ value, middle.Stores other.storage value → before.Stores other.storage value
  /-- The step advances the storage frontier by at most one root, so a fresh
  root of the middle world still lies above every source support address. -/
  nextRootBound : before.nextRoot ≤ middle.nextRoot
  located : before.Located other.storage → middle.Located other.storage
  type : ∀ term, AddressType program.declarations before other.storage term →
    AddressType program.declarations middle other.storage term
  permitted : Permitted before other.authority other.access other.storage →
    Permitted middle other.authority other.access other.storage
  /-- Owned-access handoff is only observed for an erased allocation port, which
  is the one formal whose readiness reads an owned permission. -/
  permittedOwned : (∃ identity type, other.formal = .allocation identity type) →
    Permitted before other.authority .owned other.storage →
      Permitted middle other.authority .owned other.storage
  claim : AllocationClaim before other.authority other.storage →
    AllocationClaim middle other.authority other.storage
  loans : ∀ identity loan, before.loans.get identity = some loan →
    ∃ current, middle.loans.get identity = some current ∧ current.permissionState = loan.permissionState
  loanRegion : ∀ identity loan, before.loans.get identity = some loan →
    ∃ current, middle.loans.get identity = some current ∧ current.region = loan.region
  borrowRegion : ∀ address regionId, other.authority.BorrowRegion before address regionId →
    other.authority.BorrowRegion middle address regionId
  regionState : middle.liveRegions = before.liveRegions ∧ middle.nextRegion = before.nextRegion
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
    (valid : before.WellFormed)
    (observation : StepObservation program footprint region before middle other)
    (ready : other.ReadyFor program before footprint) :
    other.ReadyFor program middle footprint := by
  cases other with
  | mk origin formal storage authority access =>
    cases formal with
    | resident localSlot =>
      obtain ⟨value,stored,initialized,type,handoff,permission⟩ := ready
      exact ⟨value,observation.stores value stored,initialized,type,
        handoff.frame_input valid (observation.value localSlot value rfl stored).1
          (observation.value localSlot value rfl stored).2
          (observation.framePermitted localSlot value rfl stored),
        observation.permitted permission⟩
    | storage identity type =>
      obtain ⟨locatedType,located,permission⟩ := ready
      exact ⟨observation.type type locatedType,observation.located located,observation.permitted permission⟩
    | allocation identity type =>
      obtain ⟨owned,locatedType,claim,authorityForm⟩ := ready
      refine ⟨owned,observation.type type locatedType,observation.claim claim,?_⟩
      rcases authorityForm with ⟨loan,loanAt⟩ | ⟨backing,guard,guarded,permission⟩
      · exact Or.inl ⟨loan,loanAt⟩
      · exact Or.inr ⟨backing,guard,guarded,
          observation.permittedOwned ⟨identity,type,rfl⟩ permission⟩
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
        exact ⟨layout,AllocationRequest.same_regions request observation.regionState.1
          observation.regionState.2⟩
      · simp only [InvocationInput.StorageRequest,if_neg owned]
        simp only [InvocationInput.StorageRequest,if_neg owned] at request
        obtain ⟨loanRegion,layout,borrowed,sourceType,request⟩ := request
        exact ⟨loanRegion,layout,observation.borrowRegion storage loanRegion borrowed,
          observation.type localSlot.type sourceType,
          AllocationRequest.same_regions request observation.regionState.1 observation.regionState.2⟩
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
      exact ⟨a,i,c.referenceView after parent (ReferenceAccess ac loan.mode),ReferenceAccess ac loan.mode,
        .referent nested reference (by rw [loans]; exact found)
          (by rw [World.Stores] at stored ⊢; rw [reads]; exact stored) located⟩
  | @resource carrier current access binding target path resident prior member stored located ih =>
      obtain ⟨a,i,c,ac,nested⟩ := ih
      exact ⟨a,i,c.resourceView after binding ac,ResourceAccess ac binding,
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

/-- The owned-access half of a ready allocation port. -/
theorem Kernel.InvocationInput.ReadyFor.allocation_access {program : RuntimeProgram} {world : World}
    {footprint : List Address} {input : InvocationInput} {identity : Identity} {type : Term}
    (ready : input.ReadyFor program world footprint) (formal : input.formal = .allocation identity type) :
    input.access = .owned := by
  cases input with
  | mk origin actual storage authority access =>
    cases actual with
    | allocation identity' type' => simpa using ready.1
    | resident localSlot => exact absurd formal (by simp)
    | storage identity' type' => exact absurd formal (by simp)
    | loan identity' type' => exact absurd formal (by simp)

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

theorem World.RecordedGuardsFramed.of_row_relation {before after : World}
    (rows : World.RowRelation before after) : before.RecordedGuardsFramed after := by
  intro identity loan found
  obtain ⟨current,selected,shape⟩ := rows.forward identity loan found
  rw [selected,Option.map_some,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.2.2.2]

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
    (regionState : middle.liveRegions = before.liveRegions ∧ middle.nextRegion = before.nextRegion)
    (permissionRows : ∀ identity loan, before.loans.get identity = some loan →
      ∃ current, middle.loans.get identity = some current ∧ current.permissionState = loan.permissionState)
    (regionRows : ∀ identity loan, before.loans.get identity = some loan →
      ∃ current, middle.loans.get identity = some current ∧ current.region = loan.region)
    (ownedAccess : (∃ identity type, other.formal = .allocation identity type) → other.access = .owned)
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
  stores := fun _ stored => World.Stores.of_roots roots stored
  storesBack := fun _ stored => World.Stores.of_roots roots.symm stored
  nextRootBound := nextRootBound
  located := World.Located.of_roots roots
  type := fun _ located => AddressType.roots_congr roots located
  permitted := fun permission => permitted _ _ _ (Or.inl ⟨rfl,rfl,Or.inl ⟨rfl,permission⟩⟩) permission
  permittedOwned := fun guard permission => by
    have same : other.access = .owned := ownedAccess guard
    exact permitted _ _ _ (Or.inl ⟨rfl,rfl,Or.inl ⟨same.symm,by rw [same]; exact permission⟩⟩) permission
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
  /-- No recorded root below the frontier has an allocation or external home. -/
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

theorem BindsInputAt.stepFrame {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before middle : World} {input : InvocationInput}
    {binding : Binding} (valid : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding middle) :
    StepFrame before middle := by
  cases bound with
  | lent ready borrowed resident stored initialized type permission lent =>
    cases input with
    | mk origin formal storage authority access =>
      cases lent with
      | owned => exact absurd rfl borrowed
      | lent modes sourceStored borrowRegion allocProof formed =>
        cases formed with
        | borrow stored' referentType initialized' regionLive admitted ready' permitted' vacant
            destinationType parentEq written =>
          refine StepFrame.of_rootFrame valid ?_ ?_
          · refine ((RootFrame.of_allocates allocProof
                (InternalRoot.temporaryHome activation scope)).trans
              (RootFrame.of_write_at written (Allocates.fresh_root allocProof).1 ?_)).congr rfl
            intro root found
            refine InternalRoot.of_home (Allocates.created_home allocProof root ?_)
              (InternalRoot.temporaryHome activation scope)
            rw [(Allocates.fresh_root allocProof).1]
            exact found
          · intro id apart
            rw [Table.get_set_other _ _ _ _ (by rw [Allocates.nextLoan allocProof]; exact apart),
              Allocates.loans allocProof]
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
    (valid : before.WellFormed) (batch : value.BatchCompatible before middle)
    (framed : value.SupportFramed before middle) (resources : value.ResourcesRecorded before)
    {authority : Authority} {requested : Access} {address : Address}
    (observed : value.ObservedViews middle access authority requested address) :
    value.ObservedViews before access authority requested address := by
  rcases observed with
    ⟨identity,current,viewAccess,loan,reached,found,atAuthority,atRequested,atAddress⟩ |
    ⟨residentValue,current,incoming,binding,reached,member,atAuthority,atRequested,atAddress⟩
  · obtain ⟨carrier,reachable,head⟩ := reached
    obtain ⟨beforeCarrier,beforeReachable,beforeHead⟩ :=
      (Value.ReachableReference.frame_batch (authority := .owner) valid resources trivial batch framed).mpr
        ⟨carrier,reachable,head⟩
    obtain ⟨original,originalFound,shape⟩ :=
      batch.rows.selected_before ⟨beforeCarrier,beforeReachable,beforeHead⟩ found
    have fields := Loan.permissionState_eq_iff.mp shape
    have guardsFrame : current.guardLoans middle = current.guardLoans before :=
      (beforeReachable.recorded (authority := .owner) valid resources trivial).guards_framed batch.guards
    refine Or.inl ⟨identity,current,viewAccess,original,⟨beforeCarrier,beforeReachable,beforeHead⟩,
      originalFound,?_,?_,?_⟩
    · rw [atAuthority,← fields.2.2.2.1]
      exact Authority.referenceView_of_guardLoans guardsFrame identity (ReferenceAccess viewAccess loan.mode)
    · rw [atRequested,← fields.2.2.2.1]
    · rw [atAddress,← fields.2.2.1]
  · have beforeReached : value.ReachableResident before .owner access residentValue current incoming :=
      (Value.ReachableResident.frame_batch (authority := .owner) valid resources trivial batch framed).mpr reached
    have guardsFrame : current.guardLoans middle = current.guardLoans before :=
      (beforeReached.recorded (authority := .owner) valid resources trivial).guards_framed batch.guards
    refine Or.inr ⟨residentValue,current,incoming,binding,beforeReached,member,?_,?_,?_⟩
    · rw [atAuthority]
      exact Authority.resourceView_of_guardLoans guardsFrame binding incoming
    · exact atRequested
    · exact atAddress

/-- Every authority one pending input's permission reading names is recorded in
the source world, so its compatibility is re-read from the source rows. -/
theorem InvocationInput.ReadsPermission.recorded {world : World}
    {other : InvocationInput} (valid : world.WellFormed) (recorded : other.authority.Recorded world.loans)
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
      have currentRecorded := carrierReached.recorded (authority := .owner) valid
        (resident localSlot value formal stored) trivial
      rw [atAuthority]
      exact currentRecorded.referenceView valid found (ReferenceAccess viewAccess loan.mode)
    · have currentRecorded := reached.recorded (authority := .owner) valid
        (resident localSlot value formal stored) trivial
      obtain ⟨bnode,baccess,breached⟩ := reached.rebase .owner .shared
      rw [atAuthority]
      exact currentRecorded.resourceView valid
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
    (resident : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesRecorded before)
    {authority : Authority} {access : Access} {address : Address}
    (reads : other.ReadsPermission middle authority access address) :
    other.ReadsPermission before authority access address := by
  rcases reads with ⟨authorityEq,addressEq,first⟩ | ⟨localSlot,value,formal,stored,views⟩
  · rcases first with ⟨accessEq,permission⟩ | ⟨allocationFormal,accessEq,permission⟩
    · subst authority
      subst address
      subst access
      exact Or.inl ⟨rfl,rfl,Or.inl ⟨rfl,
        Permitted.of_frame valid middleValid frame recorded bound permission⟩⟩
    · subst authority
      subst address
      subst access
      exact Or.inl ⟨rfl,rfl,Or.inr ⟨allocationFormal,rfl,
        Permitted.of_frame valid middleValid frame recorded bound permission⟩⟩
  · have storedBefore := observation.storesBack value stored
    obtain ⟨batch,framed⟩ := observation.value localSlot value formal storedBefore
    exact Or.inr ⟨localSlot,value,formal,storedBefore,
      Value.ObservedViews.backward valid batch framed (resident localSlot value formal storedBefore) views⟩

theorem InvocationInput.ReadsClaim.backward {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before middle : World} {other : InvocationInput}
    (valid : before.WellFormed) (_middleValid : middle.WellFormed) (frame : StepFrame before middle)
    (observation : StepObservation program footprint region before middle other)
    (recorded : other.authority.Recorded before.loans) (bound : other.storage.root < before.nextRoot)
    (resident : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesRecorded before)
    {authority : Authority} {address : Address}
    (reads : other.ReadsClaim middle authority address) : other.ReadsClaim before authority address := by
  rcases reads with ⟨authorityEq,addressEq,claim⟩ | ⟨localSlot,value,formal,stored,claims⟩
  · subst authority
    subst address
    refine Or.inl ⟨rfl,rfl,AllocationClaim.of_frame valid frame bound ?_ claim⟩
    intro anchor atAnchor
    obtain ⟨loan,found⟩ := recorded.parentLoan atAnchor
    exact World.loanBounds valid found
  · have storedBefore := observation.storesBack value stored
    obtain ⟨batch,framed⟩ := observation.value localSlot value formal storedBefore
    have resources := resident localSlot value formal storedBefore
    obtain ⟨residentValue,current,incoming,reached,binding,member,atAuthority,atAddress⟩ := claims
    exact Or.inr ⟨localSlot,value,formal,storedBefore,
      ⟨residentValue,current,incoming,
        (Value.ReachableResident.frame_batch (authority := .owner) valid resources trivial batch framed).mpr reached,
        binding,member,atAuthority,atAddress⟩⟩

theorem InvocationInput.ReadsCustody.backward {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before middle : World} {other : InvocationInput}
    (valid : before.WellFormed) (_frame : StepFrame before middle)
    (observation : StepObservation program footprint region before middle other)
    (resident : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesRecorded before)
    {authority : Authority} (reads : other.ReadsCustody middle authority) :
    other.ReadsCustody before authority := by
  rcases reads with authorityEq | ⟨localSlot,value,formal,stored,custody⟩
  · exact Or.inl authorityEq
  · have storedBefore := observation.storesBack value stored
    obtain ⟨batch,framed⟩ := observation.value localSlot value formal storedBefore
    obtain ⟨residentValue,current,incoming,reached,binding,member,atAuthority⟩ := custody
    exact Or.inr ⟨localSlot,value,formal,storedBefore,
      ⟨residentValue,current,incoming,
        (Value.ReachableResident.frame_batch (authority := .owner) valid
          (resident localSlot value formal storedBefore) trivial batch framed).mpr reached,
        binding,member,atAuthority⟩⟩

theorem InvocationInput.RetainsSupport.backward {program : RuntimeProgram} {footprint : List Address}
    {region : Identity} {before middle : World} {other : InvocationInput}
    (valid : before.WellFormed) (_frame : StepFrame before middle)
    (observation : StepObservation program footprint region before middle other)
    (resident : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesRecorded before)
    {address : Address} (retained : other.RetainsSupport middle address) :
    other.RetainsSupport before address := by
  obtain ⟨localSlot,value,formal,stored,supported⟩ := retained
  have storedBefore := observation.storesBack value stored
  obtain ⟨batch,framed⟩ := observation.value localSlot value formal storedBefore
  exact ⟨localSlot,value,formal,storedBefore,
    (Value.Support.frame_batch valid (resident localSlot value formal storedBefore) batch framed).mpr supported⟩

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
      otherRecorded otherBound residentRecorded reads
    exact Authority.LoanCompatible.frame valid frame
      (InvocationInput.ReadsPermission.recorded valid otherRecorded residentRecorded readsBefore)
      (compatible.permission referent mode guards kind
        (InvocationInput.FreshRow.frame valid frame headRecorded fresh) authority access address readsBefore)
  claim := by
    intro parent freshOwning authority address reads claim anchor atAnchor
    have residentRecorded : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value → value.ResourcesRecorded before :=
      fun localSlot value formal stored => (otherAccessible localSlot value formal stored).resourcesRecorded
    have readsBefore := InvocationInput.ReadsClaim.backward valid middleValid frame observation
      otherRecorded otherBound residentRecorded reads
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
    have residentRecorded : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value → value.ResourcesRecorded before :=
      fun localSlot value formal stored => (otherAccessible localSlot value formal stored).resourcesRecorded
    exact compatible.custody identity (InvocationInput.CustodyMoved.frame valid frame headRecorded moved) authority
      (InvocationInput.ReadsCustody.backward valid frame observation residentRecorded reads)
  clear := fun address member => compatible.clear address member
  support := by
    intro address retained
    have residentRecorded : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
        before.Stores other.storage value → value.ResourcesRecorded before :=
      fun localSlot value formal stored => (otherAccessible localSlot value formal stored).resourcesRecorded
    obtain ⟨localSlot,value,formal,storedBefore,supportedBefore⟩ :=
      InvocationInput.RetainsSupport.backward valid frame observation residentRecorded retained
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

/-- The guard list of one authority reads only the loan table, so any update
that retains the table's rows retains it. This is the recordness-free
complement of `StepFrame.guards`. -/
theorem Authority.guardLoans_congr {before after : World} (loans : after.loans = before.loans)
    (authority : Authority) : authority.guardLoans after = authority.guardLoans before := by
  induction authority with
  | owner => rfl
  | loan identity => simp only [Authority.guardLoans,loans]
  | shared backing ih => exact ih
  | guarded backing carrier ih => simp only [Authority.guardLoans,ih,loans]

/-- The three facts one still-pending input needs at the current world. -/
def InputFramed (program : RuntimeProgram) (world : World) (input : InvocationInput) : Prop :=
  input.authority.Recorded world.loans ∧ input.storage.root < world.nextRoot ∧
  (∀ (localSlot : Local) (value : Value), input.formal = .resident localSlot →
    world.Stores input.storage value → value.ResourcesAccessible program world input.access)

/-- Every pending input fact is retained by one actual binding step: the row
is retained below the loan frontier, the storage frontier only grows, and the
stored value's graph is framed by the observation. -/
theorem InputFramed.frame {program : RuntimeProgram} {footprint : List Address} {region : Identity}
    {before middle : World} {other : InvocationInput}
    (valid : before.WellFormed) (observation : StepObservation program footprint region before middle other)
    (facts : InputFramed program before other) : InputFramed program middle other := by
  refine ⟨?_,?_,?_⟩
  · exact facts.1.transport (fun identity loan found =>
      let ⟨current,selected,_⟩ := observation.loans identity loan found
      ⟨current,selected⟩)
  · exact Nat.lt_of_lt_of_le facts.2.1 observation.nextRootBound
  · intro localSlot value formal stored
    have prior := observation.storesBack value stored
    exact Value.ResourcesAccessible.frame_input valid (observation.value localSlot value formal prior).1
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
    (otherReady : other.ReadyFor program before footprint)
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
      (Nat.le_of_eq nextRootEq.symm) regionState
      (fun id loan found => StepFrame.row_of_before valid frame found)
      (fun id loan found =>
        let ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
        ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩)
      (fun ⟨id,ty,equals⟩ =>
        Glorious.Language.Kernel.InvocationInput.ReadyFor.allocation_access
          otherReady equals)
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
    (otherReady : other.ReadyFor program before footprint)
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
      (Nat.le_of_eq nextRootEq.symm) regionState
      (fun id loan found => StepFrame.row_of_before valid frame found)
      (fun id loan found =>
        let ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
        ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩)
      (fun ⟨id,ty,equals⟩ =>
        Glorious.Language.Kernel.InvocationInput.ReadyFor.allocation_access
          otherReady equals)
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
    (otherReady : other.ReadyFor program before footprint)
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
      (Nat.le_of_eq nextRootEq.symm) regionState
      (fun id loan found => StepFrame.row_of_before valid frame found)
      (fun id loan found =>
        let ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
        ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩)
      (fun ⟨id,ty,equals⟩ =>
        Glorious.Language.Kernel.InvocationInput.ReadyFor.allocation_access
          otherReady equals)
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
    (otherReady : other.ReadyFor program before footprint)
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
      (Nat.le_of_eq nextRootEq.symm) regionState
      (fun id loan found => StepFrame.row_of_before valid frame found)
      (fun id loan found =>
        let ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
        ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩)
      (fun ⟨id,ty,equals⟩ =>
        Glorious.Language.Kernel.InvocationInput.ReadyFor.allocation_access
          otherReady equals)
      (fun authority access address reads permission => forward authority access address reads permission)
      claimChannel compatibleChannel
      (fun _ _ _ _ => Value.SupportFramed.of_roots rfl) framePermittedChannel
  | shared _backingEq _parentEq _rowFound _live _kind _mode _referent =>
    exact Glorious.Language.Kernel.StepObservation.of_loans (middle := before) rfl
      (Nat.le_refl _) ⟨rfl,rfl⟩
      (fun _ _ found => ⟨_,found,rfl⟩)
      (fun _ _ found => ⟨_,found,rfl⟩)
      (fun ⟨id,ty,equals⟩ =>
        Glorious.Language.Kernel.InvocationInput.ReadyFor.allocation_access
          otherReady equals)
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

/-- The observation of one actual invocation lending step: a handle value at a
fresh root plus one restoring row at the loan frontier. -/
theorem StepObservation.of_lendsResident {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {input : InvocationInput} {footprint : List Address}
    {other : InvocationInput} {lease : Option InvocationLease} {authority : Authority}
    (valid : before.WellFormed) (frame : StepFrame before after)
    (borrowed : input.access ≠ .owned) (residentFormal : input.formal.IsResident)
    (permission : Permitted before input.authority input.access input.storage)
    (lent : LendsResident program activation scope region before input.storage input.authority input.access
      lease authority after)
    (independent : input.IndependentOf program footprint before other)
    (otherReady : other.ReadyFor program before footprint)
    (otherBound : other.storage.root < before.nextRoot)
    (_otherAccessible : ∀ (localSlot : Local) (value : Value), other.formal = .resident localSlot →
      before.Stores other.storage value → value.ResourcesAccessible program before other.access) :
    StepObservation program footprint region before after other := by
  cases input with
  | mk origin inputFormal inputStorage inputAuthority inputAccess =>
    cases lent with
    | owned => exact absurd rfl borrowed
    | lent modes sourceStored borrowRegion allocProof formed =>
      rename_i lentMode lentValue lentHandle lentAllocated lentLayout lentRegion
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
          Authority.guardLoans_congr allocatedLoans inputAuthority
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
        have fresh : InvocationInput.FreshRow before
            ⟨origin,inputFormal,inputStorage,inputAuthority,inputAccess⟩ inputStorage lentMode
            (inputAuthority.guardLoans before) .restoring := by
          obtain ⟨localSlot,formal'⟩ := Kernel.InputFormal.exists_resident_of_isResident residentFormal
          rw [InvocationInput.FreshRow,formal']
          refine ⟨borrowed,rfl,rfl,?_,rfl⟩
          cases inputAccess <;> simp_all
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
                (independent.permission inputStorage lentMode (inputAuthority.guardLoans before) .restoring
                  fresh authority' access address reads))
        refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · intro value' stored'
          rw [World.Stores] at stored' ⊢
          rw [readWhole]
          exact stored'
        · intro value' stored'
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
        · intro permitted'
          exact formedPermitted other.authority other.access other.storage
            (Or.inl ⟨rfl,rfl,Or.inl ⟨rfl,permitted'⟩⟩)
            (afterPermitted other.authority other.access other.storage permitted')
        · intro allocationFormal permitted'
          exact formedPermitted other.authority .owned other.storage
            (Or.inl ⟨rfl,rfl,Or.inr ⟨allocationFormal,rfl,permitted'⟩⟩)
            (afterPermitted other.authority .owned other.storage permitted')
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
          exact StepFrame.row_of_before valid frame found
        · intro id loan found
          let ⟨current,selected,shape⟩ := StepFrame.row_of_before valid frame found
          exact ⟨current,selected,(Loan.permissionState_eq_iff.mp shape).2.2.2.2.1⟩
        · intro address regionId borrowed'
          exact Authority.BorrowRegion.transport stepLocations
            (World.fresh_loan_region (before := lentAllocated) (after := loanStepWorld lentAllocated
              (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
              inputStorage inputAuthority lentMode lentRegion) allocatedValid stepLoans)
            (Authority.BorrowRegion.allocates valid allocProof borrowed')
        · refine ⟨?_,?_⟩
          · exact (FormsLoan.region_state formed').1.trans (Allocates.region_state allocProof).1
          · exact (FormsLoan.region_state formed').2.trans (Allocates.region_state allocProof).2
        · intro localSlot value' formal' stored'
          have handoffBefore : value'.HandoffReady program before other.access footprint :=
            (InvocationInput.ReadyFor.resident otherReady (by rw [formal']; trivial) stored').2.2.1
          have handoffAllocated : value'.HandoffReady program lentAllocated other.access footprint :=
            Allocates.handoffReady valid allocProof handoffBefore
          have framedSecond : value'.SupportFramed lentAllocated
              (loanStepWorld lentAllocated
                (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
                inputStorage inputAuthority lentMode lentRegion) := by
            intro address supported
            refine ⟨?_,?_⟩
            · exact (World.read_of_roots (before := writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
                (after := loanStepWorld lentAllocated
                  (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
                  inputStorage inputAuthority lentMode lentRegion) rfl address).trans
                (World.read_root_other (before := lentAllocated)
                  (after := writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
                  (mutation := lentHandle) written
                  (fun same => by
                    have beforeSupported := (Value.Support.frame allocatedLoans
                      (Allocates.supportFramed valid allocProof handoffBefore.1)).mpr supported
                    rw [handleRoot] at same
                    exact absurd same (Nat.ne_of_lt
                      (Value.Support.root_bound valid handoffBefore.1 beforeSupported))))
            · change Option.map Root.location
                  ((writtenWorld lentAllocated lentHandle writtenRoot writtenValue).roots.get address.root) =
                Option.map Root.location (lentAllocated.roots.get address.root)
              exact World.write_locations written address.root
          exact ⟨Value.BatchCompatible.of_fresh_loan (before := before)
              (after := loanStepWorld lentAllocated
                (writtenWorld lentAllocated lentHandle writtenRoot writtenValue)
                inputStorage inputAuthority lentMode lentRegion) valid locationsWhole loansWhole
              handoffBefore.1.2.1 parentBound
              (fun _ _ _ _ _ _ => Or.inl (fun same => by cases same)),
            (Allocates.supportFramed valid allocProof handoffBefore.1).trans allocatedLoans framedSecond⟩
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
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro value' stored'
      exact (World.Stores.write_disjoint_iff installEq destinationApart).mp
        ((World.Stores.write_disjoint_iff clearedEq sourceApart).mp
          ((Allocates.stores_iff valid allocation).mp stored'))
    · intro value' stored'
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
    · intro permitted'
      exact movedPermitted other.authority other.access other.storage
        (afterPermitted other.authority other.access other.storage permitted')
    · intro allocationFormal permitted'
      exact movedPermitted other.authority .owned other.storage
        (afterPermitted other.authority .owned other.storage permitted')
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
    · refine ⟨?_,?_⟩
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
      exact StepObservation.of_lendsResident valid frame borrowed resident permission lent independent
        otherReady otherBound otherAccessible
  | owned ready owning resident stored type allocated transferred =>
      exact StepObservation.of_ownedTransfer valid frame owning resident allocated transferred
        independent otherReady otherBound licensed otherAccessible
  | storage ready formal locatedType claimed =>
      exact StepObservation.of_storageClaim valid frame formal claimed independent otherReady
        otherAccessible
  | allocation ready formal owning locatedType transferred =>
      exact StepObservation.of_allocationTransfer valid frame formal owning transferred independent
        otherReady otherAccessible
  | guardedAllocation ready formal owning guarded locatedType claimed =>
      exact StepObservation.of_guardedClaim valid frame formal owning ⟨_,_,guarded⟩ claimed independent
        otherReady otherAccessible
  | loan ready formal owning locatedType transferred =>
      exact StepObservation.of_storageLoanTransfer valid frame formal owning transferred independent
        otherReady otherAccessible


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
      refine ⟨InvocationInput.readyFor_of_observation valid
        (observe other member (separate other member)) (prepared.ready.2.2 other
          (List.mem_cons_of_mem input member)).1,?_⟩
      exact (prepared.ready.2.2 other (List.mem_cons_of_mem input member)).2
  · intro other member
    exact InvocationInput.storageRequest_of_observation (observe other member (separate other member))
      (prepared.requests other (List.mem_cons_of_mem input member))
  · intro other member
    exact InputFramed.frame valid (observe other member (separate other member))
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

/-- Receiver lending transports along the entry lifetime. -/
theorem Execution.lendsReceiver_callee {program : Kernel.Program}
    {first second : Execution.Context} {before after : World} {address : Address}
    {authority permission : Authority} {access : Access} {lease : Option InvocationLease}
    (activation : first.activation = second.activation) (scope : first.scope = second.scope)
    (region : first.region = second.region)
    (lent : Execution.LendsReceiver program first before address authority access lease permission after) :
    Execution.LendsReceiver program second before address authority access lease permission after := by
  rw [Execution.LendsReceiver] at lent ⊢
  rw [activation,scope,region] at lent
  exact lent

/-- Invocation preparation transports along the entry lifetime: its only use of
the callee context is the receiver lending. -/
theorem Execution.preparesEntry_callee_context {program : Kernel.Program}
    {first second : Execution.Context} {function : Kernel.Function} {before after : World}
    {source : Execution.EntrySource} {inputs : List Kernel.InvocationInput}
    (activation : first.activation = second.activation) (scope : first.scope = second.scope)
    (region : first.region = second.region)
    (prepared : Execution.PreparesEntry program first function before source inputs after) :
    Execution.PreparesEntry program second function before source inputs after := by
  cases prepared with
  | supplied => exact .supplied
  | resident callable instanceArguments lent captures consumedReceiver =>
      exact .resident callable instanceArguments
        (Execution.lendsReceiver_callee activation scope region lent) captures consumedReceiver
  | contextual callable instanceArguments witnessed reserved lentReceiver lentWitness reservedLent
      consumedReceiver consumedAvailability =>
      exact .contextual callable instanceArguments witnessed reserved
        (Execution.lendsReceiver_callee activation scope region lentReceiver)
        (Execution.lendsReceiver_callee activation scope region lentWitness)
        reservedLent consumedReceiver consumedAvailability

/-- The ordinary entry endpoint. The source admission states the invocation
preparation directly at the entry context the caller will select, for whatever
environment the ordered binder produces; the binder then either completes every
input or stops at the first physically exhausted one, the receiver shell is
consumed from the world the binder produced, and the result is the real
Execution.EnterWorldAttempt. -/
theorem Kernel.EntryBatch.enterWorldAttempt {program : Kernel.Program} {before : Execution.State}
    {caller : Execution.Context} {function : Kernel.Function} {source : Execution.EntrySource}
    {withRegion prepared : World} {inputs : List InvocationInput}
    (consumed : World → World)
    (callee : Execution.Context)
    (calleeLifetime : callee.activation = before.nextActivation ∧
      callee.scope = before.world.nextRegion ∧ callee.region = before.world.nextRegion)
    (declared : ∃ declaration, program.declarations.function function.declaration = some declaration)
    (prepares : Execution.PreparesEntry program callee function withRegion source inputs prepared)
    (fresh : FreshRegion before.world before.world.nextRegion withRegion)
    (preparedValid : prepared.WellFormed)
    (incoming : IncomingResources program function prepared inputs)
    (product : InvocationInputsCompatible program (inputs.flatMap InvocationInput.clearedStorage)
      before.world.nextRegion prepared inputs)
    (facts : ∀ input ∈ inputs, InputFramed program prepared input)
    (nodup : inputs.Nodup)
    (finishes : ∀ bound, Execution.FinishesEntry bound source (consumed bound))
    (callerUnsafe : function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) :
    ∃ context after outcome,
      Execution.EnterWorldAttempt program before caller function source context after outcome := by
  obtain ⟨declaration,declared⟩ := declared
  obtain ⟨environment,bound,outcome,attempt,framed⟩ :=
    Kernel.BatchPrepared.attemptFor (recipient := .activation before.nextActivation)
      (activation := before.nextActivation) (scope := before.world.nextRegion)
      (region := before.world.nextRegion) prepared inputs [] preparedValid
      (Kernel.BatchPrepared.of_compatible product facts nodup)
  have transported : Execution.PreparesEntry program
      ⟨environment,declaration.header.module,before.nextActivation,before.world.nextRegion,
        before.world.nextRegion,function.entryScope before.world.nextRegion before.nextBrand,false,
        [⟨function.declaration,environment⟩]⟩ function withRegion source inputs prepared :=
    Execution.preparesEntry_callee_context calleeLifetime.1 calleeLifetime.2.1 calleeLifetime.2.2
      prepares
  refine ⟨⟨environment,declaration.header.module,before.nextActivation,before.world.nextRegion,
      before.world.nextRegion,function.entryScope before.world.nextRegion before.nextBrand,false,
      [⟨function.declaration,environment⟩]⟩,
    (match outcome with | .complete => consumed bound | .exhausted => bound), outcome,
    withRegion,prepared,inputs,environment,declaration,bound,
    declared,fresh,transported,incoming,attempt,?_,rfl,callerUnsafe⟩
  cases outcome
  · exact finishes bound
  · rfl


/-- The receiver-shell consumption producers: the exact source-level evidence a
caller has after the ordered binder produced its world. -/
theorem Execution.FinishesEntry.of_resident {before after : World}
    {receiver : ResolvedPlace} {access : Access}
    {arguments : List Kernel.InvocationInput}
    (finished : Execution.FinishesReceiver before receiver access after) :
    Execution.FinishesEntry before (.resident receiver access arguments) after :=
  .resident finished

theorem Execution.FinishesEntry.of_contextual {before after : World}
    {receiver witness : ResolvedPlace} {access witnessAccess : Access}
    {inputs : List Kernel.InvocationInput}
    (finished : Execution.FinishesReceiver before receiver access after) :
    Execution.FinishesEntry before (.contextual receiver access witness witnessAccess inputs) after :=
  .contextual finished

/-- A lent receiver needs no poststate evidence at all: the admitted lending
access itself finishes the entry at the very world the binder produced. -/
theorem Execution.FinishesEntry.lent_resident {before : World} {receiver : ResolvedPlace}
    {access : Access} {arguments : List Kernel.InvocationInput} (lentAccess : access ≠ .owned) :
    Execution.FinishesEntry before (.resident receiver access arguments) before :=
  .resident (.lent lentAccess)

theorem Execution.FinishesEntry.lent_contextual {before : World} {receiver witness : ResolvedPlace}
    {access witnessAccess : Access} {inputs : List Kernel.InvocationInput}
    (lentAccess : access ≠ .owned) :
    Execution.FinishesEntry before (.contextual receiver access witness witnessAccess inputs) before :=
  .contextual (.lent lentAccess)




/-- Address overlap is symmetric, so an apartness obligation can be read from
either side. -/
theorem Address.not_overlaps_symm {first second : Address} (apart : ¬ first.Overlaps second) :
    ¬ second.Overlaps first :=
  fun overlap => apart ⟨overlap.1.symm,overlap.2.1.symm,
    overlap.2.2.elim (fun same => Or.inr same) (fun same => Or.inl same)⟩

/-- The caller's receiver port lies outside every pending binding's write and
referent set, and below the prepared storage frontier. This is the structural
prestate admission that lets the receiver shell and its owner permission be
framed across the ordered fold. -/
structure Kernel.ReceiverApart (receiver : Address) (world : World)
    (inputs : List InvocationInput) : Prop where
  storage : ∀ input ∈ inputs, ¬ input.storage.Overlaps receiver
  frontier : receiver.root < world.nextRoot



/-- Setting one entry to a hole keeps a list of holes all holes. -/
theorem List.allNone_set {α : Type} {list : List (Option α)}
    (all : ∀ value ∈ list, value = none) (index : Nat) :
    ∀ value ∈ list.set index none, value = none := by
  induction list generalizing index with
  | nil => intro value member; simp at member
  | cons head tail ih =>
      have headNone : head = none := all head List.mem_cons_self
      cases index with
      | zero =>
          intro value member
          simp only [List.set_cons_zero,List.mem_cons] at member
          rcases member with same | later
          · simp [same]
          · exact all value (List.mem_cons_of_mem head later)
      | succ index =>
          intro value member
          simp only [List.set_cons_succ,List.mem_cons] at member
          rcases member with same | later
          · simp [same,headNone]
          · exact ih (fun value member => all value (List.mem_cons_of_mem head member)) index value later

/-- A clearing write inside a value all of whose fields are holes leaves every
field of the result a hole: this is the projection the receiver shell needs
when a pending capture's storage lies under the receiver. -/
theorem Value.replace_fields_none {before after : Value} {index : Nat} {path : List Nat}
    (written : before.replace (index :: path) none = some after)
    (noneBefore : ∀ field ∈ before.fields, field = none) :
    ∀ field ∈ after.fields, field = none := by
  rcases Value.replace_cons_shape written with
    ⟨slot,found,⟨_,rfl⟩ | ⟨child,changed,atSlot,_,rfl⟩⟩
  · intro field member
    have member' : field ∈ List.set before.fields index none := by
      simpa only [Value.fields,Value.withFields] using member
    exact List.allNone_set noneBefore index field member'
  · exact absurd (noneBefore slot (List.mem_of_getElem? found))
      (by rw [atSlot]; simp)


/-- The receiver shell the entry must preserve: a stored value with the callable
head, the consumed liveness flag, every field a hole and no resources, plus the
owner permission at the receiver address. -/
def Kernel.ReceiverFramed (world : World) (receiver : Address) (authority : Authority)
    (head : ValueHead) : Prop :=
  (∃ value, world.Stores receiver value ∧ value.head = head ∧ value.shellLive = false ∧
    (∀ field ∈ value.fields, field = none) ∧ value.resources = []) ∧
  Permitted world authority .owned receiver



/-- The carrier identities a borrowed authority opens through, outermost first:
the recursion-friendly view of the authority data that the formed row's guard
list must miss. -/
def Kernel.authorityCarriers : Authority → List Identity
  | .owner => []
  | .loan _ => []
  | .shared backing => Kernel.authorityCarriers backing
  | .guarded backing carrier => carrier :: Kernel.authorityCarriers backing

/-- A receiver owner permission survives a formed fresh row. The three
pre-state facts about the forming authority are: the authority's own parent
identity is absent from the formed row's guard list, every carrier identity of
the authority is absent from it, and every carrier's live referent is apart from
the formed row's referent. These are properties of the authority data that forms
the row (the same data FormsLoan's own compatibility input speaks about), not
poststate callbacks. -/
theorem Kernel.Permitted.owner_compatible {world : World} {authority : Authority}
    {receiver referent : Address} {mode : Mutability} {guards : List Identity}
    (permitted : Permitted world authority .owned receiver)
    (apart : ¬ receiver.Overlaps referent)
    (parentAbsent : ∀ identity, authority.parentLoan = some identity → identity ∉ guards)
    (absent : ∀ carrier, carrier ∈ Kernel.authorityCarriers authority → carrier ∉ guards)
    (referentApart : ∀ carrier loan, carrier ∈ Kernel.authorityCarriers authority →
      world.loans.get carrier = some loan → ¬ loan.referent.Overlaps referent) :
    authority.LoanCompatible world .owned receiver referent mode guards := by
  revert permitted apart parentAbsent absent referentApart
  induction authority with
  | owner =>
      intro permitted apart parentAbsent absent referentApart
      exact fun overlap => False.elim (apart overlap)
  | loan identity =>
      intro permitted apart parentAbsent absent referentApart
      refine ⟨fun overlap => False.elim (apart overlap),
        fun member => False.elim (absurd member (parentAbsent identity rfl))⟩
  | shared backing _ =>
      intro permitted apart parentAbsent absent referentApart
      exact absurd permitted.2.1 (by simp)
  | guarded backing carrier ih =>
      intro permitted apart parentAbsent absent referentApart
      refine ⟨ih permitted.2.1 apart (fun identity same => parentAbsent identity same)
        (fun carrier' member => absent carrier' (List.mem_cons_of_mem carrier member))
        (fun carrier' loan member found =>
          referentApart carrier' loan (List.mem_cons_of_mem carrier member) found),?_⟩
      · intro loan found
        exact ⟨fun overlap => False.elim (referentApart carrier loan List.mem_cons_self found overlap),
          fun member => False.elim (absurd member (absent carrier List.mem_cons_self))⟩


end Kernel