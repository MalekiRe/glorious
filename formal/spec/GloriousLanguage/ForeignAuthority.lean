import GloriousLanguage.ForeignRootFraming
import GloriousLanguage.InvocationLeaseCleanup

/-! The actual foreign protocol preserves unexposed internal storage. This
uses authority reachability and the actual mutation producers, not an assertion
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
  | subplace =>
    rename_i place address prior relationship location ih
    exact .subplace ih relationship location

theorem Reachable.avoids_root {program : Language.Program} {world : World}
    {seeds : ResolvedPlace → Prop} {place : ResolvedPlace} {root : Identity}
    (reachable : Reachable program world seeds place)
    (outside : ∀ seed, seeds seed → seed.address.root ≠ root)
    (loans : ∀ id loan, world.loans.get id = some loan → loan.live = true → loan.referent.root ≠ root) :
    place.address.root ≠ root := by
  induction reachable with
  | seed present => exact outside _ present
  | project _ resolved ih => exact resolved.avoids_root ih loans
  | subplace =>
    rename_i place address prior relationship location ih
    exact fun same => ih (relationship.1.trans same)

theorem AccessSeed.avoids_internal_during {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial current : World} {session : ForeignSession} {id : Identity} {root : Root} {place : ResolvedPlace}
    (_bound : id < initial.nextRoot) (selected : current.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (seed : AccessSeed program model contract initial current session place) : place.address.root ≠ id := by
  rcases seed with ⟨present,_⟩ |
      ⟨registration,member,active,retained,rfl,custodied,rootFound,domain,found,home⟩ |
      ⟨externalClause,parentNone,rootFound,domain,found,home,domainEq,memberDomain⟩
  · exact known _ present
  · intro same
    have selectedAt : current.roots.get registration.owner.root = some root := same ▸ selected
    have equal : rootFound = root := Option.some.inj ((World.root_found found).1.symm.trans selectedAt)
    subst rootFound
    exact home.elim (internalHome domain).1 (internalHome domain).2
  · intro same
    have selectedAt : current.roots.get place.address.root = some root := same ▸ selected
    have equal : rootFound = root := Option.some.inj ((World.root_found found).1.symm.trans selectedAt)
    subst rootFound
    exact (internalHome domain).2 home

theorem Accessible.avoids_internal_during {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial current : World} {session : ForeignSession} {id : Identity} {root : Root} {place : ResolvedPlace}
    (bound : id < initial.nextRoot) (selected : current.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (loans : ∀ key loan, current.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id)
    (accessible : Accessible program model contract initial current session place) : place.address.root ≠ id :=
  accessible.avoids_root (fun _ seed => seed.avoids_internal_during bound selected internalHome known) loans

theorem Accessible.avoids_internal {program : Kernel.Program} {model : Model} {contract : Contract}
    {world : World} {session : ForeignSession} {id : Identity} {root : Root} {place : ResolvedPlace}
    (well : world.WellFormed) (selected : world.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (loans : ∀ key loan, world.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id)
    (accessible : Accessible program model contract world world session place) : place.address.root ≠ id :=
  accessible.avoids_internal_during (World.root_bound well selected) selected internalHome known loans


/- The freshness producers `Mutation.produced_fresh` and
`Mutations.published_fresh` live in `ForeignEvolution`; the mutations below are
their call sites. -/

/-- Exact root framing is derived from each actual mutation's selected
inputs. This includes vacant roots and does not consume FramePreserved. -/
theorem Mutation.private_root_unchanged {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial before after : World} {session : ForeignSession} {mutationAction : MutationAction}
    {id : Identity} {root : Root}
    (changed : Mutation program (Policy program model contract initial session) before mutationAction after)
    (bound : id < initial.nextRoot) (counter : initial.nextRoot ≤ before.nextRoot)
    (selected : before.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (loans : ∀ key loan, before.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id) :
    after.roots.get id = before.roots.get id := by
  have inaccessible (place : ResolvedPlace) (accessible : Accessible program model contract initial before session place) :
      id ≠ place.address.root := (accessible.avoids_internal_during bound selected internalHome known loans).symm
  have unwritable (address : Address) (writable : Writable program model contract initial before session address) :
      id ≠ address.root := inaccessible _ writable.2.choose_spec.1
  have oldBound := Nat.lt_of_lt_of_le bound counter
  cases changed with
  | allocate _ _ allocated => exact allocated.roots_other oldBound
  | allocateExterior _ _ allocated => exact allocated.roots_other oldBound
  | scalar writable stored => exact stored.2.2.roots_other (unwritable _ writable) (by intro source member; cases member)
  | unit writable stored => exact stored.2.roots_other (unwritable _ writable) (by intro source member; cases member)
  | pointer writable _ _ _ stored => exact stored.2.roots_other (unwritable _ writable) (by intro source member; cases member)
  | aggregate writable sources _ _ constructed =>
    exact constructed.roots_other (unwritable _ writable)
      (fun source member => inaccessible source (sources source member))
  | acquire place write acquired => exact acquired.roots_other (inaccessible _ place) (unwritable _ write)
  | borrow place write borrowed => exact borrowed.roots_other (unwritable _ write)
  | allocateBuffer _ allocated => exact allocated.roots_other oldBound
  | reallocateBuffer _ _ _ reallocated => exact reallocated.private_root oldBound selected internalHome
  | @releaseBuffer _ allocation pointer domain _ _ _ released =>
    have origin : ∃ allocation, pointer.allocation = some allocation := by
      cases released with
      | release bufferAt _ _ _ _ _ _ _ _ _ =>
        obtain ⟨allocated,_,allocationEq,_⟩ := bufferAt
        exact ⟨allocated,allocationEq⟩
    obtain ⟨allocation,origin⟩ := origin
    exact released.roots_other origin (released.avoids_internal selected internalHome origin).symm
  | rawRead _ write _ read =>
    cases read with
    | read points _ _ action =>
      rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
      · exact copied.roots_other (unwritable _ write)
      · exact moved.roots_other (internalHome.no_raw selected points).symm (unwritable _ write)
  | rawWrite source _ _ written =>
    cases written with
    | write _ _ points _ _ _ moved => exact moved.roots_other (inaccessible _ source) (internalHome.no_raw selected points).symm
  | rawBorrow _ write _ borrowed =>
    cases borrowed with
    | borrow _ _ _ _ formed => exact formed.roots_other (unwritable _ write)
  | bulkMove places writes moved =>
    exact moved.roots_other
      (fun source member => inaccessible _ (places source member))
      (fun destination member => unwritable destination.address (writes destination member).2)
  | retire _ accessible retired => exact retired.roots_other (inaccessible _ accessible)
  | endLoan ended => cases ended; rfl

/-- New logical loans cannot turn an unexposed private home into accessible
storage. Every new loan follows either an actually reachable source place or
an allocation/external raw origin; ordinary release introduces no live loan. -/
theorem Mutation.private_root {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial before after : World} {session : ForeignSession} {mutationAction : MutationAction}
    {id : Identity} {root : Root}
    (changed : Mutation program (Policy program model contract initial session) before mutationAction after)
    (bound : id < initial.nextRoot) (counter : initial.nextRoot ≤ before.nextRoot)
    (selected : before.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (loans : ∀ key loan, before.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id) :
    after.roots.get id = some root ∧
    (∀ key loan, after.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id) := by
  refine ⟨(changed.private_root_unchanged bound counter selected internalHome known loans).trans selected,?_⟩
  intro key loan found live
  rcases changed.liveLoan_origin found live with ⟨original,oldFound,oldLive,sameReferent⟩ |
      ⟨authority,accessible⟩ | ⟨pointer,type,points⟩ | fresh
  · rw [sameReferent]
    exact loans key original oldFound oldLive
  · exact accessible.avoids_internal_during bound selected internalHome known loans
  · exact internalHome.no_raw selected points
  · intro same
    rw [same] at fresh
    exact absurd fresh (Nat.not_le_of_lt (Nat.lt_of_lt_of_le bound counter))

theorem ForeignSession.advance_known {session : ForeignSession} {state : List Nat} {place : ResolvedPlace}
    {produced : List ProducedResource} (known : place ∈ session.known) :
    place ∈ (session.advance produced state).known := by
  simp only [Execution.ForeignSession.known,Execution.ForeignSession.advance,List.mem_append] at known ⊢
  exact known.elim Or.inl (fun present => Or.inr (Or.inl present))

theorem ForeignSession.advance_avoids {session : ForeignSession} {state : List Nat}
    {id : Identity} {produced : List ProducedResource}
    (outside : ∀ place ∈ session.known, place.address.root ≠ id)
    (avoided : ∀ resource ∈ produced, resource.place.address.root ≠ id) :
    ∀ place ∈ (session.advance produced state).known, place.address.root ≠ id := by
  intro place known same
  simp only [Execution.ForeignSession.known,Execution.ForeignSession.advance,List.mem_append] at known
  rcases known with operand | exposed | fresh
  · exact outside place (List.mem_append_left _ operand) same
  · exact outside place (List.mem_append_right _ exposed) same
  · obtain ⟨resource,member,shape⟩ := List.mem_filterMap.mp fresh
    by_cases chosen : resource.recipient = ClaimCustody.host session.call.destination.root
    · have samePlace : resource.place = place := Option.some.inj (by simpa [chosen] using shape)
      exact avoided resource member (by rw [samePlace]; exact same)
    · simp [chosen] at shape

theorem Mutations.private_root {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial : World} {session : ForeignSession} {custody : ClaimCustody} {id : Identity} {root : Root}
    (bound : id < initial.nextRoot) (known : ∀ place ∈ session.known, place.address.root ≠ id) :
    ∀ (before after : World) (produced : List ProducedResource) (actions : List MutationAction),
      Mutations program custody
        (fun produced => Policy program model contract initial (session.advance produced session.state))
        before produced actions after →
      (∀ resource ∈ produced, resource.place.address.root ≠ id) →
      initial.nextRoot ≤ before.nextRoot → before.roots.get id = some root → InternalHome root →
      (∀ key loan, before.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id) →
      after.roots.get id = some root ∧
        (∀ key loan, after.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id) := by
  intro beforeCase afterCase producedCase actionsCase changed
  induction changed with
  | refl =>
    intro freshInitial counter selected internalHome loans
    exact ⟨selected,loans⟩
  | cons first rest ih =>
    intro freshInitial counter selected internalHome loans
    rename_i beforeWorld afterWorld middleCase accumulatedCase actionCase restCase
    have oldBound : id < beforeWorld.nextRoot := Nat.lt_of_lt_of_le bound counter
    have advanced : ∀ place ∈ (session.advance accumulatedCase session.state).known,
        place.address.root ≠ id :=
      ForeignSession.advance_avoids (session := session)
        (state := session.state) (produced := accumulatedCase) known
        (fun resource member => freshInitial resource member)
    obtain ⟨middleRoot,middleLoans⟩ :=
      first.private_root (session := session.advance accumulatedCase session.state)
        bound counter selected internalHome advanced loans
    have freshNext : ∀ resource ∈ accumulatedCase ++ actionCase.produced custody,
        resource.place.address.root ≠ id := by
      intro resource member
      rcases List.mem_append.mp member with earlier | own
      · exact freshInitial resource earlier
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le oldBound (first.produced_fresh own))
    exact ih freshNext (Nat.le_trans counter first.homeExtension.counter) middleRoot internalHome middleLoans

/-- Every actual host transition preserves the complete hidden root and
therefore its residents. Only mutation laws are used: even an everywhere-true
writable predicate supplies no access to an unexposed internal root. -/
theorem Model.Lawful.private_resident {program : Kernel.Program} {model : Model}
    {contract : Contract} {imported : Import} {before after : World} {session : ForeignSession}
    {observation next : List Nat} {action : HostAction} {id : Identity} {root : Root}
    {address : Address} {value : Value}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    {actions : List MutationAction}
    (step : model.step session.call.binding.declaration before session observation actions after action next)
    (rootAt : before.roots.get id = some root) (internalHome : InternalHome root)
    (known : ∀ place ∈ session.known, place.address.root ≠ id)
    (loans : ∀ key loan, before.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id)
    (addressRoot : address.root = id) (resident : before.Resident address value) : after.Stores address value := by
  have changed := (lawful.step session imported contract before observation actions after action next
    selected well active step).1
  have roots := (changed.private_root (World.root_bound well rootAt) known
    before after [] actions (by intro resource member; simp at member) (Nat.le_refl _) rootAt internalHome loans).1
  simpa only [World.Stores,World.read,World.root,addressRoot,roots,rootAt] using World.resident_iff_stores.mp resident

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

/-- Concrete control-boundary invariant for a hidden root, initialized or
vacant. The source control proof establishes private placement and lack of
incoming references; actual host mutations preserve the entire same root. -/
def InternalRoot (world : World) (session : ForeignSession) (id : Identity) (root : Root) : Prop :=
  world.roots.get id = some root ∧ InternalHome root ∧
  (∀ place ∈ session.known, place.address.root ≠ id) ∧
  (∀ key loan, world.loans.get key = some loan → loan.live = true → loan.referent.root ≠ id)

/-- Resident privacy is a projection of the same root invariant. -/
def InternalResident (world : World) (session : ForeignSession) (address : Address) (value : Value) : Prop :=
  world.Stores address value ∧
  ∃ root, InternalRoot world session address.root root

theorem Model.Lawful.advance_internal_root {program : Kernel.Program} {model : Model}
    {contract : Contract} {imported : Import} {before after : World} {session : ForeignSession}
    {observation next : List Nat} {action : HostAction} {id : Identity} {root : Root}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    {actions : List MutationAction}
    (step : model.step session.call.binding.declaration before session observation actions after action next)
    (privateRoot : InternalRoot before session id root) :
    InternalRoot after
      (session.advance (TransactionOutputs (.host session.call.destination.root) actions) next) id root := by
  obtain ⟨rootAt,internalHome,known,loans⟩ := privateRoot
  have bound := World.root_bound well rootAt
  have changed := (lawful.step session imported contract before observation actions after action next
    selected well active step).1
  obtain ⟨roots,loansAfter⟩ := changed.private_root bound known before after [] actions
    (by intro resource member; simp at member) (Nat.le_refl _) rootAt internalHome loans
  exact ⟨roots,internalHome,
    ForeignSession.advance_avoids (session := session) (state := next)
      (produced := TransactionOutputs (.host session.call.destination.root) actions) known
      (fun resource member => Nat.ne_of_gt (Nat.lt_of_lt_of_le bound (changed.published_fresh member))),
    loansAfter⟩

theorem Model.Lawful.advance_internal {program : Kernel.Program} {model : Model}
    {contract : Contract} {imported : Import} {before after : World} {session : ForeignSession}
    {observation next : List Nat} {action : HostAction} {address : Address} {value : Value}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    {actions : List MutationAction}
    (step : model.step session.call.binding.declaration before session observation actions after action next)
    (privateResident : InternalResident before session address value) :
    InternalResident after (session.advance (TransactionOutputs (.host session.call.destination.root) actions) next) address value := by
  obtain ⟨stored,root,privateRoot⟩ := privateResident
  exact ⟨lawful.private_resident well selected active step privateRoot.1 privateRoot.2.1 privateRoot.2.2.1 privateRoot.2.2.2 rfl
    (World.resident_iff_stores.mpr stored),root,lawful.advance_internal_root well selected active step privateRoot⟩

theorem InternalRoot.returned {world : World} {session : ForeignSession} {id : Identity} {root : Root}
    {result : Address} {state : List Nat} (privateRoot : InternalRoot world session id root)
    (separate : result.root ≠ id) : InternalRoot world (session.returned result state) id root :=
  ⟨privateRoot.1,privateRoot.2.1,ForeignSession.returned_avoids privateRoot.2.2.1 separate,privateRoot.2.2.2⟩

theorem InternalResident.returned {world : World} {session : ForeignSession} {address result : Address}
    {value : Value} {state : List Nat} (privateResident : InternalResident world session address value)
    (separate : result.root ≠ address.root) : InternalResident world (session.returned result state) address value :=
  ⟨privateResident.1,privateResident.2.choose,privateResident.2.choose_spec.returned separate⟩

theorem Step.continue_internal_root {program : Kernel.Program} {model : Model} {before after : State}
    {event : Option Event} {session continued : ForeignSession} {next following : Code} {id : Identity} {root : Root}
    (lawful : model.Lawful program) (well : before.world.WellFormed)
    (step : Step program model before event after)
    (task : before.task = .foreign session next) (result : after.task = .foreign continued following)
    (privateRoot : InternalRoot before.world session id root) : InternalRoot after.world continued id root := by
  cases step with
  | enter original => cases original.symm.trans task
  | host original _ selected active changed =>
    cases original.symm.trans task
    cases result
    exact lawful.advance_internal_root well selected active changed privateRoot
  | result => cases result
  | callback => cases result
  | callbackResult original => cases original.symm.trans task
  | callbackReturned original => cases original.symm.trans task
  | fault => cases result

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
  obtain ⟨stored,root,privateRoot⟩ := privateResident
  have kept := step.continue_internal_root lawful well task result privateRoot
  refine ⟨?_,root,kept⟩
  simpa only [World.Stores,World.read,World.root,kept.1,privateRoot.1] using stored

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

/-- Arbitrarily many lawful host steps preserve the exact private root and
full world typing, including live vacant handles and their storage metadata.
No post-state framing assertion is used as a host admission premise. -/
theorem HostRun.internal_root {program : Kernel.Program} {model : Model} {before after : State}
    {events : List Event} {session continued : ForeignSession} {next following : Code}
    {id : Identity} {root : Root}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (run : HostRun program model before events after)
    (task : before.task = .foreign session next) (result : after.task = .foreign continued following)
    (privateRoot : InternalRoot before.world session id root) :
    Typing.WorldTyped program after.world ∧ InternalRoot after.world continued id root := by
  induction run generalizing session next with
  | refl original =>
    cases task.symm.trans result
    exact ⟨typed,privateRoot⟩
  | cons original step rest ih =>
    obtain ⟨middle,next,middleTask⟩ := rest.start
    have middleTyped := step.worldTyped valid inventory lawful typed
    have middlePrivate := step.continue_internal_root lawful typed.1 task middleTask privateRoot
    exact ih middleTyped middleTask result middlePrivate

theorem HostRun.internal_resident {program : Kernel.Program} {model : Model} {before after : State}
    {events : List Event} {session continued : ForeignSession} {next following : Code}
    {address : Address} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (run : HostRun program model before events after)
    (task : before.task = .foreign session next) (result : after.task = .foreign continued following)
    (privateResident : InternalResident before.world session address value) :
    Typing.WorldTyped program after.world ∧ InternalResident after.world continued address value := by
  obtain ⟨stored,root,privateRoot⟩ := privateResident
  obtain ⟨afterTyped,kept⟩ := run.internal_root valid inventory lawful typed task result privateRoot
  refine ⟨afterTyped,?_,root,kept⟩
  simpa only [World.Stores,World.read,World.root,kept.1,privateRoot.1] using stored

end Foreign

namespace Kernel

theorem LendsResident.handle_fresh {program : RuntimeProgram} {before after : World}
    {activation scope region : Identity} {address : Address} {authority permission : Authority}
    {access : Access} {lease : InvocationLease}
    (lent : LendsResident program activation scope region before address authority access (some lease) permission after) :
    lease.handle.root = before.nextRoot := by
  cases lent with
  | lent _ _ _ allocated _ => cases allocated; rfl

/-- No pre-existing loan points to a fresh hidden handle, and its new loan
points to the invocation input rather than back into its own handle slot. -/
theorem LendsResident.handle_no_incoming {program : RuntimeProgram} {before after : World}
    {activation scope region : Identity} {address : Address} {authority permission : Authority}
    {access : Access} {lease : InvocationLease} (well : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access (some lease) permission after) :
    ∀ id loan, after.loans.get id = some loan → loan.live = true → loan.referent.root ≠ lease.handle.root := by
  have fresh := lent.handle_fresh
  cases lent with
  | lent _ stored _ allocated borrowed =>
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
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned)
    (known : ∀ place ∈ session.known, place.address.root < before.nextRoot) :
    Typing.WorldTyped program after ∧
    ∃ witness value, lease = some witness ∧ value.head = .reference witness.loan ∧
      Foreign.InternalResident after session witness.handle value := by
  have afterTyped := lent.worldTyped valid inventory typed
  obtain ⟨witness,owner,mode,type,sourceRegion,selected,_,stored⟩ := lent.lease_resident borrowed
  rw [selected] at lent
  obtain ⟨actual,root,same,rootAt,home,_,_⟩ := lent.lease_owned borrowed
  have identity : witness = actual := Option.some.inj same
  subst actual
  refine ⟨afterTyped,witness,_,selected,rfl,stored,root,(World.root_found rootAt).1,Foreign.InternalHome.temporary home,?_,
    lent.handle_no_incoming typed.1⟩
  intro place member same
  exact Nat.ne_of_lt (known place member) (same.trans lent.handle_fresh)

end Kernel
end Glorious.Language
