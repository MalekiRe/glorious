import GloriousLanguage.DropDispatch
import GloriousLanguage.DropInvocation
import GloriousLanguage.SemanticPreservation
import GloriousLanguage.InvocationLeaseCleanup
import GloriousLanguage.CleanupDrain

/-! Normal destructor return consumes the restored current receiver, not its
pre-call owner. The administrative tail relinquishes the unit's custody, drains
its pending returns and retires private unit/handle storage before selecting
current receiver fields. Source Drop bodies may recurse or diverge. -/
namespace Glorious.Language

/-- A fieldless unit root cannot also contain a non-unit receiver. Thus the
cleanup's physical disjointness follows from its real stored inhabitants. -/
theorem World.stores_outside_unit {world : World} {unitAddress address : Address}
    {root : Root} {owner : Identity} {value : Value}
    (unitFound : world.root unitAddress = some root)
    (unitValue : root.value = some (.resident owner .unit .unit true []))
    (stored : world.Stores address value) (nonunit : value.type ≠ .unit) :
    unitAddress.root ≠ address.root := by
  intro same
  obtain ⟨addressRoot,addressFound⟩ := (Option.bind_eq_some_iff.mp stored).imp fun _ found => found.1
  have unitAt := (World.root_found unitFound).1
  have addressAt := (World.root_found addressFound).1
  have equal : addressRoot = root := Option.some.inj (addressAt.symm.trans (same ▸ unitAt))
  subst addressRoot
  have resident : (Value.resident owner .unit .unit true []).atPath address.fields = some value := by
    simpa [World.Stores,World.read,addressFound,unitValue] using stored
  cases path : address.fields with
  | nil =>
    have equal : (.resident owner .unit .unit true []) = value := by
      simpa only [path,Value.atPath,Option.some.injEq] using resident
    exact nonunit (equal ▸ rfl)
  | cons => simp [path,Value.atPath,Value.fields] at resident


namespace Execution

/-- The returned hook consumes original custody discharge and retry admission,
executes the real pending-return drain, then retires its private unit and handle.
Only resident-backed caller carriers justify preserved loan permissions. -/
theorem hookReturned_administrative {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context outer : Context} {result address handle : Address}
    {authority : Authority} {loan : Identity} {next : Task} {rest : List Frame}
    {receiver : Value} {resultRoot handleRoot : Root} {unitOwner : Identity} {original : Loan}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .yield context result)
    (frames : before.frames = .hook outer address authority handle loan next :: rest)
    (stored : before.world.Stores address receiver)
    (ended : before.world.loans.get loan = some { original with live := false })
    (destructor : original.kind = .destructor)
    (resultFound : before.world.root result = some resultRoot) (resultWhole : result.fields = [])
    (unitValue : resultRoot.value = some (.resident unitOwner .unit .unit true []))
    (resultPrivate : CanEndStorage before.world result.root)
    (discharge : before.world.CustodyDischarge (.resident unitOwner))
    (returns : before.world.CustodyReleaseReady program (.resident unitOwner))
    (separate : result.root ≠ address.root)
    (handleFound : before.world.roots.get handle.root = some handleRoot)
    (handleLive : handleRoot.live = true) (handleVacant : handleRoot.value = none)
    (handlePrivate : CanEndStorage before.world handle.root) :
    ∃ trace after,
      Run program host before (.destroy result unitOwner :: (trace ++ [.retire result.root,.retire handle.root])) after ∧
      after.task = .destroyFields outer address authority (List.range receiver.fields.length).reverse next ∧
      after.frames = rest ∧ after.world.Stores address receiver ∧
      after.world.loans.get loan = some { original with live := false } ∧
      (∀ permission access, Permitted before.world permission access address →
        (∀ id ∈ permission.carriers, before.world.References id) → Permitted after.world permission access address) ∧
      Typing.WorldTyped program after.world ∧
      (∃ event following, LocalStep program after event following) := by
  have ⟨resultAt,resultLive,_⟩ := World.root_found resultFound
  have different : handle.root ≠ result.root := by
    intro same
    have equal := Option.some.inj (handleFound.symm.trans (same ▸ resultAt))
    have impossible := handleVacant.symm.trans (equal ▸ unitValue)
    cases impossible
  have handed := World.CustodyHandedOff.of_discharge discharge
  let requested := before.world.RequestReturns (.resident unitOwner)
  have relinquished : RelinquishesCustody before.world (.resident unitOwner) requested := .of_handedOff handed
  let cleared : World := { requested with roots := requested.roots.set result.root { resultRoot with value := none } }
  have requestedResult : requested.root result = some resultRoot := resultFound
  have written : requested.write result none = some cleared := by
    simp [World.write,requestedResult,resultWhole,cleared]
  have unitStored : before.world.Stores result (.resident unitOwner .unit .unit true []) := by
    simp [World.Stores,World.read,resultFound,unitValue,resultWhole,Value.atPath]
  have requestedUnit : requested.Stores result (.resident unitOwner .unit .unit true []) := unitStored
  have unitPermission : Permitted before.world .owner .owned result :=
    resultPrivate.place_permission resultWhole resultFound
  have unitDisposable : MayDispose program.declarations (.resident unitOwner .unit .unit true []) := by
    intro path resident inside
    cases inside with
    | root =>
      exact ⟨fun _ => ⟨_,PrincipalOf.unit _,by simp [Principal.MayDiscard,Principal.Permits]⟩,fun hook impossible => by
        rcases impossible with ⟨_,_,_,same,_,_⟩ | ⟨_,same⟩ <;> cases same⟩
    | field selected _ => simp [Value.fields] at selected
  let fields := Task.destroyFields outer address authority (List.range receiver.fields.length).reverse next
  let close := Task.closeLoan loan fields
  let retireH := Task.retire handle.root close
  let retireR := Task.retire result.root retireH
  let started := { before with frames := rest,task := Task.destroy outer result .owner retireR }
  let structural := { started with task := Task.destroyFields outer result .owner [] retireR }
  let shell := { structural with task := Task.finishShell result .owner retireR }
  let vacant := { shell with world := cleared,task := ReleaseCustodyLoans cleared (.resident unitOwner) retireR }
  have start : LocalStep program before none started := .hookReturned task frames stored
  have noDrop : DropHook program.declarations .unit none := by
    refine Or.inr ⟨?_,rfl⟩
    intro id args impossible
    cases impossible
  have structuralStep : LocalStep program started none structural :=
    .destroyStructural (before := started) rfl unitStored unitDisposable unitPermission (Or.inr noDrop)
      (by intro id impossible; cases impossible) (by intro id impossible; cases impossible)
      (by intro id impossible; cases impossible)
  have fieldStep : LocalStep program structural none shell := .fieldsDone rfl
  have shellStep : LocalStep program shell (some (.destroy result unitOwner)) vacant :=
    .shellDone (before := shell) rfl unitStored (by simp [Value.fields]) unitPermission relinquished written
  have shellRun : CleanupRun program host started [.destroy result unitOwner] vacant :=
    .silent trivial (Or.inl structuralStep) (.silent trivial (Or.inl fieldStep)
      (.visible trivial (Or.inl shellStep) .refl))
  have queueReady := (returns.requested handed).write_empty_shell (relinquished.canEndStorage resultPrivate)
    requestedUnit (by simp [Value.fields]) (by intro id impossible; cases impossible) rfl written
  obtain ⟨drainedWorld,trace,drained,frame⟩ := CleanupRun.release_custody_returns
    (program := program) (host := host) (before := vacant) rfl
    (by simpa only [vacant,World.write_loans written] using queueReady)
  let drainedState := { vacant with world := drainedWorld,task := retireR }
  have drainedTyped : Typing.WorldTyped program drainedWorld :=
    CleanupRun.worldTyped (before := started) (after := drainedState) valid inventory typed (shellRun.append drained)
  let resultRetired : World := { drainedWorld with roots := drainedWorld.roots.set result.root { resultRoot with value := none,live := false,generation := resultRoot.generation+1 } }
  let afterWorld : World := { resultRetired with roots := resultRetired.roots.set handle.root { handleRoot with live := false,generation := handleRoot.generation+1 } }
  have retireResult : Retires drainedWorld result.root resultRetired := by
    have selected : drainedWorld.roots.get result.root = some { resultRoot with value := none } := by
      rw [congrArg World.roots frame.rest]
      exact Table.get_set _ _ _
    exact .vacant selected resultLive rfl
      (frame.canEndStorage (World.write_canEndStorage written (relinquished.canEndStorage resultPrivate)))
  have retireHandle : Retires resultRetired handle.root afterWorld := by
    have selected : resultRetired.roots.get handle.root = some handleRoot := by
      rw [Table.get_set_other _ _ _ _ different,congrArg World.roots frame.rest,World.write_roots_other written different]
      exact handleFound
    have safe := frame.canEndStorage (World.write_canEndStorage written (relinquished.canEndStorage handlePrivate))
    exact .vacant selected handleLive handleVacant
      (safe.sameHomes (by simp only [resultRetired,Table.get_set_other _ _ _ _ different]) rfl rfl)
  have clearedEnded : cleared.loans.get loan = some { original with live := false } := by
    rw [World.write_loans written,World.RequestReturns.get_eq,ended]
    simp [World.restamp,destructor]
  have loanEnded := frame.dead_retained clearedEnded rfl
  let endedResult := { drainedState with world := resultRetired,task := retireH }
  let endedHandle := { endedResult with world := afterWorld,task := close }
  let after := { endedHandle with task := fields }
  have resultStep : LocalStep program drainedState (some (.retire result.root)) endedResult := .retire rfl retireResult
  have handleStep : LocalStep program endedResult (some (.retire handle.root)) endedHandle := .retire rfl retireHandle
  have loanStep : LocalStep program endedHandle none after := .loanAlreadyEnded rfl loanEnded rfl
  have suffix : CleanupRun program host drainedState [.retire result.root,.retire handle.root] after :=
    .visible trivial (Or.inl resultStep) (.visible trivial (Or.inl handleStep) (.silent trivial (Or.inl loanStep) .refl))
  have cleanup := shellRun.append (drained.append suffix)
  have clearedStored : cleared.Stores address receiver :=
    (World.write_disjoint written (fun overlap => separate overlap.1)).trans stored
  have retained : after.world.Stores address receiver :=
    (retireHandle.read address).trans ((retireResult.read address).trans (clearedStored.loanReleaseFrame frame))
  have located : ∃ root, after.world.root address = some root :=
    (Option.bind_eq_some_iff.mp retained).imp fun _ found => found.1
  refine ⟨trace,after,.silent (Or.inl start) cleanup.run,rfl,rfl,retained,loanEnded,?_,?_,?_⟩
  · intro permission access permitted carriers
    have clearedLocated : ∃ root, cleared.root address = some root :=
      (Option.bind_eq_some_iff.mp clearedStored).imp fun _ found => found.1
    have clearedPermission := (relinquished.permitted permitted).of_same_loans
      (before := requested) (after := cleared) (World.write_loans written) clearedLocated
    have kept : ∀ id ∈ permission.carriers, cleared.References id := by
      intro id member
      exact World.write_nonreference_leaf_references requestedUnit rfl (by intro id impossible; cases impossible) written
        ((carriers id member).roots_congr (after := requested) rfl)
    exact (frame.permitted drainedTyped.1 clearedPermission kept).of_same_loans
      (before := drainedWorld) (after := after.world) rfl located
  · exact cleanup.worldTyped (before := started) valid inventory typed
  · cases selected : (List.range receiver.fields.length).reverse with
    | nil => exact ⟨none,_,.fieldsDone (context := outer) (address := address) (authority := authority)
        (next := next) (by change fields = _; simp [fields,selected])⟩
    | cons field remaining => exact ⟨none,_,.fieldNext (context := outer) (address := address) (authority := authority)
        (field := field) (fields := remaining) (next := next) (by change fields = _; simp [fields,selected])⟩

end Execution

namespace Contracts

/-- Composition with the actual normal observation. Returned-state custody
discharge, retry restoration and private-root provenance are explicit original
admission; the cleanup world and its variable drain trace are derived. -/
theorem DropContract.normal_return_cleanup {program : Kernel.Program} {host : Foreign.Model}
    {self region : Term} {hook : DeclId} {arguments : List Term}
    {declaration : FunctionDefinition} {substitution : Substitution}
    {function : Kernel.Function} {observation : Observation} {before : Execution.State}
    {context outer : Execution.Context} {result : Address} {authority : Authority}
    {loan : Identity} {next : Execution.Task} {rest : List Execution.Frame}
    {input : Kernel.InvocationInput} {inputValue : Value} {original : Loan}
    {resultRoot handleRoot : Root} {unitOwner : Identity}
    (valid : Specification.WellFormed program)
    (application : DropApplication program.declarations self region hook arguments declaration substitution)
    (contract : DropContract program self region function) (lawful : host.Lawful program)
    (observed : Observes program host function observation) (normal : observation.outcome = .normal result)
    (member : input ∈ observation.input) (inputStored : observation.before.Stores input.storage inputValue)
    (head : inputValue.head = .reference loan) (selected : observation.before.loans.get loan = some original)
    (destructor : original.kind = .destructor)
    (world : before.world = observation.after) (task : before.task = .yield context result)
    (frames : before.frames = .hook outer original.referent authority input.storage loan next :: rest)
    (resultFound : before.world.root result = some resultRoot) (resultWhole : result.fields = [])
    (unitValue : resultRoot.value = some (.resident unitOwner .unit .unit true []))
    (resultPrivate : CanEndStorage before.world result.root)
    (discharge : before.world.CustodyDischarge (.resident unitOwner))
    (returns : before.world.CustodyReleaseReady program (.resident unitOwner))
    (handleFound : before.world.roots.get input.storage.root = some handleRoot)
    (handleLive : handleRoot.live = true) (handleVacant : handleRoot.value = none)
    (handlePrivate : CanEndStorage before.world input.storage.root) :
    ∃ receiver trace after,
      observation.after.Stores original.referent receiver ∧ receiver.type = self ∧ receiver.Initialized ∧
      MayDispose program.declarations receiver ∧
      Execution.Run program host before (.destroy result unitOwner :: (trace ++ [.retire result.root,.retire input.storage.root])) after ∧
      after.task = .destroyFields outer original.referent authority (List.range receiver.fields.length).reverse next ∧
      after.frames = rest ∧ after.world.Stores original.referent receiver ∧
      DropBorrowReturned self after.world loan original ∧
      (∀ permission access, Permitted observation.after permission access original.referent →
        (∀ id ∈ permission.carriers, observation.after.References id) →
        Permitted after.world permission access original.referent) ∧
      Typing.WorldTyped program after.world ∧
      (∃ event following, Execution.LocalStep program after event following) := by
  have returned := contract.normal_borrow_returned lawful observed normal member inputStored head selected
  rw [← world] at returned
  obtain ⟨ended,receiver,stored,receiverType,initialized⟩ := returned
  have typed : Typing.WorldTyped program before.world := world ▸ (observed.worldTyped valid.declarations valid.inventory lawful).2
  obtain ⟨principal,capability,discard⟩ := application.capability
  have disposable := (typed.2.1 _ _ (World.resident_iff_stores.mpr stored)).mayDispose valid.declarations valid.inventory initialized
    (receiverType.symm ▸ capability) discard
  have nonunit : receiver.type ≠ .unit := by
    cases application with
    | selected drops _ _ _ _ _ _ _ _ _ =>
      rcases drops with ⟨id,args,data,nominal,_,_⟩ | ⟨_,impossible⟩
      · rw [receiverType,nominal]
        intro impossible
        cases impossible
      · cases impossible
  obtain ⟨trace,after,run,fields,afterFrames,retained,loanEnded,permissions,afterTyped,progress⟩ :=
    Execution.hookReturned_administrative valid.declarations valid.inventory typed task frames stored ended destructor
      resultFound resultWhole unitValue resultPrivate discharge returns
      (World.stores_outside_unit resultFound unitValue stored nonunit) handleFound handleLive handleVacant handlePrivate
  exact ⟨receiver,trace,after,world ▸ stored,receiverType,initialized,disposable,run,fields,afterFrames,retained,
    ⟨loanEnded,receiver,retained,receiverType,initialized⟩,by simpa only [world] using permissions,afterTyped,progress⟩

end Contracts
end Glorious.Language
