import GloriousLanguage.ForeignEvolution
import GloriousLanguage.InvocationLeaseCleanup

/-! The actual foreign protocol preserves unexposed internal storage. This
uses authority reachability and the checked frame contract, not an assertion
that a host's arbitrary writable predicate happens to exclude private slots. -/
namespace Glorious.Language

open Kernel Execution Memory

theorem Kernel.ResolvesProjections.avoids_root {world : World} {environment : Environment}
    {base address : Address} {authority permission : Authority} {projections : List Projection} {root : Identity}
    (resolved : ResolvesProjections world environment base authority projections address permission)
    (outside : base.root ≠ root)
    (loans : ∀ id loan, world.loans.get id = some loan → loan.live = true → loan.referent.root ≠ root) :
    address.root ≠ root := by
  induction resolved with
  | nil => exact outside
  | field _ _ _ ih => exact ih outside
  | vacantField => exact outside
  | index _ _ _ _ _ _ _ ih => exact ih outside
  | dereference _ _ _ _ found live _ _ ih => exact ih (loans _ _ found live)

namespace Foreign

theorem Reachable.mono {program : Language.Program} {world : World}
    {first second : ResolvedPlace → Prop} {place : ResolvedPlace}
    (reachable : Reachable program world first place)
    (included : ∀ seed, first seed → second seed) : Reachable program world second place := by
  induction reachable with
  | seed present => exact .seed (included _ present)
  | project _ resolved ih => exact .project ih resolved
  | pointer _ stored initialized permitted type head points ih =>
    exact .pointer ih stored initialized permitted type head points

theorem Reachable.avoids_root {program : Language.Program} {world : World}
    {seeds : ResolvedPlace → Prop} {place : ResolvedPlace} {root : Identity}
    (reachable : Reachable program world seeds place)
    (outside : ∀ seed, seeds seed → seed.address.root ≠ root)
    (loans : ∀ id loan, world.loans.get id = some loan → loan.live = true → loan.referent.root ≠ root)
    (pointers : ∀ pointer address type, PointsTo program world pointer address type → address.root ≠ root) :
    place.address.root ≠ root := by
  induction reachable with
  | seed present => exact outside _ present
  | project _ resolved ih => exact resolved.avoids_root ih loans
  | pointer _ _ _ _ _ _ points _ => exact pointers _ _ _ points

/-- Allocation/external objects can be explicitly shared with a host.
Internal logical homes require an actual source handoff instead. -/
def InternalHome (root : Root) : Prop :=
  ∀ domain, root.home ≠ .allocation domain ∧ root.home ≠ .external domain

theorem InternalHome.temporary {root : Root} {activation scope : Identity}
    (home : root.home = .temporary activation scope) : InternalHome root := by
  intro domain
  simp [home]

theorem InternalHome.no_raw {program : Language.Program} {world : World} {id : Identity} {root : Root}
    (selected : world.roots.get id = some root) (internalHome : InternalHome root)
    {pointer : RawPointer} {address : Address} {type : Term}
    (points : PointsTo program world pointer address type) : address.root ≠ id := by
  intro same
  obtain ⟨other,_,found,_,_,domain,_,home⟩ := points.2.2.2
  have identity := Option.some.inj ((World.root_found found).1.symm.trans (same ▸ selected))
  subst other
  exact home.elim (internalHome domain).1 (internalHome domain).2

theorem AccessSeed.avoids_internal_during {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial current : World} {session : ForeignSession} {id : Identity} {root : Root} {place : ResolvedPlace}
    (bound : id < initial.nextRoot) (selected : current.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (seed : AccessSeed program model contract initial current session place) : place.address.root ≠ id := by
  rcases seed with present | ⟨registration,_,_,_,rfl,other,domain,found,home⟩ |
      ⟨_,other,domain,found,home,_,_⟩ | ⟨fresh,_,_,_⟩
  · exact known _ present
  · intro same
    have identity := Option.some.inj ((World.root_found found).1.symm.trans (same ▸ selected))
    subst other
    exact home.elim (internalHome domain).1 (internalHome domain).2
  · intro same
    have identity := Option.some.inj ((World.root_found found).1.symm.trans (same ▸ selected))
    subst other
    exact (internalHome domain).2 home
  · intro same
    exact Nat.not_le_of_gt bound (same ▸ fresh)

theorem Accessible.avoids_internal_during {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial current : World} {session : ForeignSession} {id : Identity} {root : Root} {place : ResolvedPlace}
    (bound : id < initial.nextRoot) (selected : current.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (loans : ∀ key loan, current.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id)
    (accessible : Accessible program model contract initial current session place) : place.address.root ≠ id :=
  accessible.avoids_root (fun _ seed => seed.avoids_internal_during bound selected internalHome known)
    loans (fun _ _ _ points => internalHome.no_raw selected points)

theorem Accessible.avoids_internal {program : Kernel.Program} {model : Model} {contract : Contract}
    {world : World} {session : ForeignSession} {id : Identity} {root : Root} {place : ResolvedPlace}
    (well : world.WellFormed) (selected : world.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (loans : ∀ key loan, world.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id)
    (accessible : Accessible program model contract world world session place) : place.address.root ≠ id :=
  accessible.avoids_internal_during (World.root_bound well selected) selected internalHome known loans

/-- Every actual host transition preserves every resident of an internal
root absent from its handoffs and reference reachability. This holds even
when `contract.writable` is the everywhere-true predicate. -/
theorem Model.Lawful.private_resident {program : Kernel.Program} {model : Model}
    {contract : Contract} {imported : Import} {before after : World} {session : ForeignSession}
    {observation next : List Nat} {action : HostAction} {id : Identity} {root : Root}
    {address : Address} {value : Value}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (step : model.step session.call.binding.declaration before session observation after action next)
    (rootAt : before.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (loans : ∀ key loan, before.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id)
    (addressRoot : address.root = id) (resident : before.Resident address value) : after.Stores address value := by
  have frame := (lawful.step session imported contract before observation after action next
    selected well active step).2.2.1
  apply frame address value resident
  intro ancestor overlaps writable
  obtain ⟨authority,accessible,_⟩ := writable.2
  exact accessible.avoids_internal well rootAt internalHome known loans (overlaps.1.trans addressRoot)

theorem _root_.Glorious.Language.World.HomeExtension.internal_root {before after : World} {id : Identity} {root : Root}
    (changed : before.HomeExtension after) (bound : id < before.nextRoot)
    (selected : before.roots.get id = some root) (internalHome : InternalHome root) :
    ∃ current, after.roots.get id = some current ∧ InternalHome current := by
  have homes := changed.homes id bound
  rw [selected] at homes
  obtain ⟨current,found,home⟩ := Option.map_eq_some_iff.mp homes
  exact ⟨current,found,fun domain => by simpa only [home] using internalHome domain⟩

/-- New logical loans cannot turn an unexposed private home into accessible
storage. Every new loan follows either an actually reachable source place or
an allocation/external raw origin; ordinary release introduces no live loan. -/
theorem Mutation.private_root {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial before after : World} {session : ForeignSession} {id : Identity} {root : Root}
    (changed : Mutation program (Policy program model contract initial session) before after)
    (bound : id < initial.nextRoot) (counter : initial.nextRoot ≤ before.nextRoot)
    (selected : before.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (loans : ∀ key loan, before.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id) :
    (∃ current, after.roots.get id = some current ∧ InternalHome current) ∧
    (∀ key loan, after.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id) := by
  refine ⟨changed.homeExtension.internal_root (Nat.lt_of_lt_of_le bound counter) selected internalHome,?_⟩
  intro key loan found live
  rcases changed.liveLoan_origin found live with old | ⟨authority,accessible⟩ | ⟨pointer,type,points⟩
  · exact loans key loan old live
  · exact accessible.avoids_internal_during bound selected internalHome known loans
  · exact internalHome.no_raw selected points

theorem Mutations.private_root {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial before after : World} {session : ForeignSession} {id : Identity} {root : Root}
    (changed : Mutations program (Policy program model contract initial session) before after)
    (bound : id < initial.nextRoot) (counter : initial.nextRoot ≤ before.nextRoot)
    (selected : before.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (loans : ∀ key loan, before.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id) :
    (∃ current, after.roots.get id = some current ∧ InternalHome current) ∧
    (∀ key loan, after.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id) := by
  induction changed generalizing root with
  | refl => exact ⟨⟨root,selected,internalHome⟩,loans⟩
  | cons first _ ih =>
    obtain ⟨⟨middle,middleAt,middleHome⟩,middleLoans⟩ :=
      first.private_root bound counter selected internalHome known loans
    exact ih (Nat.le_trans counter first.homeExtension.counter) middleAt middleHome middleLoans

theorem FreshExposed.root_bound {before after : World} {place : ResolvedPlace}
    (exposed : place ∈ FreshExposed before after) : before.nextRoot ≤ place.address.root := by
  obtain ⟨⟨id,root⟩,_,selected⟩ := List.mem_filterMap.mp exposed
  dsimp only at selected
  split at selected
  next condition =>
    cases selected
    exact condition.1
  next => cases selected

theorem ForeignSession.advance_known {session : ForeignSession} {before after : World}
    {state : List Nat} {place : ResolvedPlace} (known : place ∈ session.known) :
    place ∈ (session.advance before after state).known := by
  simp only [Execution.ForeignSession.known,Execution.ForeignSession.advance,List.mem_append] at known ⊢
  exact known.elim Or.inl (fun present => Or.inr (Or.inl present))

theorem ForeignSession.advance_avoids {session : ForeignSession} {before after : World}
    {state : List Nat} {id : Identity}
    (outside : ∀ place ∈ session.known, place.address.root ≠ id) (bound : id < before.nextRoot) :
    ∀ place ∈ (session.advance before after state).known, place.address.root ≠ id := by
  intro place known same
  simp only [Execution.ForeignSession.known,Execution.ForeignSession.advance,List.mem_append] at known
  rcases known with operand | exposed | fresh
  · exact outside place (List.mem_append_left _ operand) same
  · exact outside place (List.mem_append_right _ exposed) same
  · exact Nat.not_le_of_gt bound (same ▸ FreshExposed.root_bound fresh)

theorem ForeignSession.returned_exposes {session : ForeignSession} {result : Address} {state : List Nat} :
    ⟨result,.owner⟩ ∈ (session.returned result state).known := by
  simp [Execution.ForeignSession.known,Execution.ForeignSession.returned]

theorem ForeignSession.returned_avoids {session : ForeignSession} {result : Address}
    {state : List Nat} {id : Identity}
    (outside : ∀ place ∈ session.known, place.address.root ≠ id) (separate : result.root ≠ id) :
    ∀ place ∈ (session.returned result state).known, place.address.root ≠ id := by
  intro place known
  simp only [Execution.ForeignSession.known,Execution.ForeignSession.returned,List.mem_append,List.mem_cons] at known
  rcases known with operand | rfl | exposed
  · exact outside place (List.mem_append_left _ operand)
  · exact separate
  · exact outside place (List.mem_append_right _ exposed)

/-- Concrete control-boundary invariant for a hidden resident. The source
control proof must establish its private placement and lack of incoming
references; the host proof establishes that the resident remains private. -/
def InternalResident (world : World) (session : ForeignSession) (address : Address) (value : Value) : Prop :=
  world.Stores address value ∧
  (∃ root, world.roots.get address.root = some root ∧ InternalHome root) ∧
  (∀ place ∈ session.known, place.address.root ≠ address.root) ∧
  (∀ key loan, world.loans.get key = some loan → loan.live = true → loan.referent.root ≠ address.root)

theorem Model.Lawful.advance_internal {program : Kernel.Program} {model : Model}
    {contract : Contract} {imported : Import} {before after : World} {session : ForeignSession}
    {observation next : List Nat} {action : HostAction} {address : Address} {value : Value}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (step : model.step session.call.binding.declaration before session observation after action next)
    (privateResident : InternalResident before session address value) :
    InternalResident after (session.advance before after next) address value := by
  obtain ⟨stored,⟨root,rootAt,internalHome⟩,known,loans⟩ := privateResident
  have bound := World.root_bound well rootAt
  have changed := (lawful.step session imported contract before observation after action next
    selected well active step).1
  obtain ⟨roots,loansAfter⟩ := changed.private_root bound (Nat.le_refl _) rootAt internalHome known loans
  exact ⟨lawful.private_resident well selected active step rootAt internalHome known loans rfl
    (World.resident_iff_stores.mpr stored),roots,ForeignSession.advance_avoids known bound,loansAfter⟩

theorem InternalResident.returned {world : World} {session : ForeignSession} {address result : Address}
    {value : Value} {state : List Nat} (privateResident : InternalResident world session address value)
    (separate : result.root ≠ address.root) : InternalResident world (session.returned result state) address value :=
  ⟨privateResident.1,privateResident.2.1,ForeignSession.returned_avoids privateResident.2.2.1 separate,
    privateResident.2.2.2⟩

/-- The actual continued host transition consumes the internal-resident
invariant. Callback return is separate: it explicitly exposes its one result,
and therefore needs the source control proof that that result is not private. -/
theorem Step.continue_internal {program : Kernel.Program} {model : Model} {before after : State}
    {event : Option Event} {session continued : ForeignSession} {next following : Code}
    {address : Address} {value : Value}
    (lawful : model.Lawful program) (well : before.world.WellFormed)
    (step : Step program model before event after)
    (task : before.task = .foreign session next) (result : after.task = .foreign continued following)
    (privateResident : InternalResident before.world session address value) :
    InternalResident after.world continued address value := by
  cases step with
  | enter original => cases original.symm.trans task
  | host original _ selected active changed =>
    cases original.symm.trans task
    cases result
    exact lawful.advance_internal well selected active changed privateResident
  | result => cases result
  | callback => cases result
  | callbackResult original => cases original.symm.trans task
  | callbackReturned original => cases original.symm.trans task
  | fault => cases result

/-- A consecutive foreign protocol phase, defined only by its actual
foreign transitions and the foreign task at both endpoints. It cannot hide
source callback execution, allocation or hidden-handle creation in a chunk. -/
inductive HostRun (program : Kernel.Program) (model : Model) : State → List Event → State → Prop where
  | refl {state session next} : state.task = .foreign session next → HostRun program model state [] state
  | cons {before middle after event events session next} : before.task = .foreign session next →
      Step program model before event middle → HostRun program model middle events after →
      HostRun program model before (event.toList ++ events) after

theorem HostRun.start {program : Kernel.Program} {model : Model} {before after : State} {events : List Event}
    (run : HostRun program model before events after) : ∃ session next, before.task = .foreign session next := by
  cases run with
  | refl task => exact ⟨_,_,task⟩
  | cons task => exact ⟨_,_,task⟩

theorem HostRun.finish {program : Kernel.Program} {model : Model} {before after : State} {events : List Event}
    (run : HostRun program model before events after) : ∃ session next, after.task = .foreign session next := by
  induction run with
  | refl task => exact ⟨_,_,task⟩
  | cons _ _ _ ih => exact ih

theorem HostRun.run {program : Kernel.Program} {model : Model} {before after : State} {events : List Event}
    (run : HostRun program model before events after) : Execution.Run program model before events after := by
  induction run with
  | refl => exact .refl
  | @cons before middle after event events session next _ step _ ih =>
    cases event with
    | none => exact .silent (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr step))))) ih
    | some => exact .visible (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr step))))) ih

/-- Arbitrarily many lawful host steps preserve the exact private resident
and full world typing. The post-state assertion is derived from the existing
mutation producers and actual frame laws; it is not a host admission premise. -/
theorem HostRun.internal_resident {program : Kernel.Program} {model : Model} {before after : State}
    {events : List Event} {session continued : ForeignSession} {next following : Code}
    {address : Address} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (run : HostRun program model before events after)
    (task : before.task = .foreign session next) (result : after.task = .foreign continued following)
    (privateResident : InternalResident before.world session address value) :
    Typing.WorldTyped program after.world ∧ InternalResident after.world continued address value := by
  induction run generalizing session next with
  | refl original =>
    cases task.symm.trans result
    exact ⟨typed,privateResident⟩
  | cons original step rest ih =>
    obtain ⟨middle,next,middleTask⟩ := rest.start
    have middleTyped := step.worldTyped valid inventory lawful typed
    have middlePrivate := step.continue_internal lawful typed.1 task middleTask privateResident
    exact ih middleTyped middleTask result middlePrivate

end Foreign

namespace Kernel

theorem LendsResident.handle_fresh {program : Language.Program} {before after : World}
    {activation scope region : Identity} {address : Address} {authority permission : Authority}
    {access : Access} {lease : InvocationLease}
    (lent : LendsResident program activation scope region before address authority access (some lease) permission after) :
    lease.handle.root = before.nextRoot := by
  cases lent with
  | lent _ _ allocated _ => cases allocated; rfl

/-- No pre-existing loan points to a fresh hidden handle, and its new loan
points to the invocation input rather than back into its own handle slot. -/
theorem LendsResident.handle_no_incoming {program : Language.Program} {before after : World}
    {activation scope region : Identity} {address : Address} {authority permission : Authority}
    {access : Access} {lease : InvocationLease} (well : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access (some lease) permission after) :
    ∀ id loan, after.loans.get id = some loan → loan.live = true → loan.referent.root ≠ lease.handle.root := by
  have fresh := lent.handle_fresh
  cases lent with
  | lent _ stored allocated borrowed =>
    have bound : address.root < before.nextRoot := by
      obtain ⟨root,_,found,_⟩ := World.resident_iff_stores.mpr stored
      exact World.root_bound well found
    intro id loan found live same
    rcases borrowed.loan_origin found with original | referent
    · have old : before.loans.get id = some loan := by simpa only [allocated.loans] using original
      have bound := World.live_loan_root_bound well old live
      exact Nat.ne_of_lt bound (same.trans fresh)
    · exact Nat.ne_of_lt bound (by simpa only [referent] using same.trans fresh)

/-- The real lending producer establishes the foreign privacy invariant for
its hidden reference owner. Existing host handoffs need only have old storage
identities; the resulting resident, home and incoming-loan exclusion are proved. -/
theorem LendsResident.internal_handle {program : Kernel.Program} {before after : World}
    {activation scope region : Identity} {address : Address} {authority permission : Authority}
    {access : Access} {lease : Option InvocationLease} {session : ForeignSession}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (lent : LendsResident program.declarations activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned)
    (known : ∀ place ∈ session.known, place.address.root < before.nextRoot) :
    Typing.WorldTyped program after ∧
    ∃ witness value, lease = some witness ∧ value.head = .reference witness.loan ∧
      Foreign.InternalResident after session witness.handle value := by
  have afterTyped := lent.worldTyped valid inventory typed
  obtain ⟨witness,owner,mode,type,selected,_,stored⟩ := lent.lease_resident borrowed
  rw [selected] at lent
  obtain ⟨actual,root,same,rootAt,home,_,_⟩ := lent.lease_owned borrowed
  have identity : witness = actual := Option.some.inj same
  subst actual
  refine ⟨afterTyped,witness,_,selected,rfl,stored,⟨root,(World.root_found rootAt).1,Foreign.InternalHome.temporary home⟩,?_,
    lent.handle_no_incoming typed.1⟩
  intro place member same
  exact Nat.ne_of_lt (known place member) (same.trans lent.handle_fresh)

end Kernel
end Glorious.Language
