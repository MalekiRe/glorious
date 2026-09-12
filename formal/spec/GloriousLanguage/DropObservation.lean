import GloriousLanguage.InvocationLifecycle

/-! Destructor contracts consume the common contextual invocation interval.
Finite, infinite and normal-return conclusions refer to those actual states,
never an isolated execution with the caller's frames erased. -/
namespace Glorious.Language.Contracts

theorem DropContract.observes_safe {program : Kernel.Program} {host : Foreign.Model}
    {self region : Term} {function : Kernel.Function} {observation : Observation}
    (contract : DropContract program self region function) (lawful : Foreign.Model.Lawful program host)
    (observed : Observes program host function observation) :
    DropTraceSafe observation.before observation.input observation.events := by
  obtain ⟨boundary,start,finish,initial,before,run,_⟩ := observed
  simpa only [before] using (contract.2.1 host observation.input boundary start observation.events finish lawful initial run).1

theorem DropContract.diverges_safe {program : Kernel.Program} {host : Foreign.Model}
    {self region : Term} {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {states : Nat → Execution.State} {events : Nat → Option Execution.Event}
    (contract : DropContract program self region function) (lawful : Foreign.Model.Lawful program host)
    (diverges : Diverges program host function inputs states events) (length : Nat) :
    DropTraceSafe (states 0).world inputs ((List.range length).filterMap events) := by
  obtain ⟨boundary,initial,steps⟩ := diverges
  exact (contract.2.1 host inputs boundary (states 0) _ (states length) lawful initial (InvocationRun.prefix steps length)).1

theorem DropContract.normal_borrow_returned {program : Kernel.Program} {host : Foreign.Model}
    {self region : Term} {function : Kernel.Function} {observation : Observation}
    {result : Address} {input : Kernel.InvocationInput} {value : Value} {id : Identity} {original : Loan}
    (contract : DropContract program self region function) (lawful : host.Lawful program)
    (observed : Observes program host function observation) (normal : observation.outcome = .normal result)
    (member : input ∈ observation.input) (stored : observation.before.Stores input.storage value)
    (head : value.head = .reference id) (loan : observation.before.loans.get id = some original) :
    DropBorrowReturned self observation.after id original :=
  contract.2.2.1 host observation lawful observed result normal input member value id original stored head loan

/-- Normal completion is the exact saved return context and ambient suffix,
before the caller's result continuation executes. -/
theorem InvocationStart.normal_observation {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {boundary : InvocationBoundary}
    {start finish : Execution.State} {events : List Execution.Event} {result : Address}
    (initial : InvocationStart program host function inputs boundary start)
    (run : InvocationRun program host boundary start events finish) (normal : boundary.Normal finish result) :
    Observes program host function ⟨inputs,start.world,events,finish.world,.normal result⟩ :=
  ⟨boundary,start,finish,initial,rfl,run,rfl,normal⟩

/-- Internally handled performances are allowed. Every pending operation
reached by an admitted hook prefix must route to its own internal delimiter,
before any ambient handler can transfer or capture the invocation's frames. -/
theorem DropContract.interval_perform_internal {program : Kernel.Program} {host : Foreign.Model}
    {self region : Term} {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {boundary : InvocationBoundary} {start finish : Execution.State} {events : List Execution.Event}
    {context : Execution.Context} {operation : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    (contract : DropContract program self region function) (lawful : host.Lawful program)
    (initial : InvocationStart program host function inputs boundary start)
    (run : InvocationRun program host boundary start events finish)
    (pending : finish.task = .perform context operation arguments payload) :
    boundary.InternalOperation program finish operation arguments payload := by
  classical
  apply Classical.byContradiction
  intro outside
  exact (contract.2.1 host inputs boundary start events finish lawful initial run).2
    operation arguments payload ⟨⟨context,pending⟩,outside⟩

/-- An admitted Drop cannot enter an escaped continuation lifecycle. The
contradiction is its actual outward request prefix, not a blanket prohibition
on all internal performance or an assumption about later caller events. -/
theorem DropContract.no_lifecycle {program : Kernel.Program} {host : Foreign.Model}
    {self region : Term} {function : Kernel.Function} {observation : LifecycleObservation}
    (contract : DropContract program self region function) (lawful : host.Lawful program) :
    ¬ LifecycleObserves program host function observation := by
  rintro ⟨captured,⟨boundary,start,pending,operation,arguments,payload,
    observed,requestOutcome,_⟩,_⟩
  obtain ⟨initial,_,run,_,outcome⟩ := observed
  have outward := requestOutcome ▸ outcome
  exact (contract.2.1 host _ boundary start observation.request.events pending lawful initial run).2
    operation arguments payload outward

end Glorious.Language.Contracts
