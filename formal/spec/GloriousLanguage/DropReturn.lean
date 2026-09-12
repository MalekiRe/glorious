import GloriousLanguage.DropDispatch
import GloriousLanguage.SemanticPreservation
import GloriousLanguage.InvocationLeaseCleanup

/-! Normal destructor return consumes the restored current receiver, not its
pre-call owner. The ordinary administrative tail destroys only the private
unit result and retires the vacant argument handle before selecting the
current receiver's fields. Arbitrary source destruction inside a hook may
recursively invoke Drop and diverge; that is not an administrative re-entry. -/
namespace Glorious.Language

/-- Loans determine authority checks once the observed storage still exists.
This local framing law does not require unrelated retired roots to stay live. -/
theorem Permitted.sameLoansAt {before after : World} {authority : Authority}
    {access : Access} {address : Address}
    (loans : after.loans = before.loans) (located : ∃ root, after.root address = some root)
    (permission : Permitted before authority access address) :
    Permitted after authority access address := by
  induction authority with
  | owner => exact ⟨located,by simpa only [loans] using permission.2⟩
  | loan id =>
    obtain ⟨_,active,found,live,root,generation,path,mode,allowed⟩ := permission
    refine ⟨located,active,by simpa only [loans] using found,live,root,generation,path,mode,?_⟩
    intro other loan found live different overlap conflict
    exact (allowed other loan (by simpa only [loans] using found) live different overlap conflict).sameLoans loans.symm
  | shared backing ih => exact ⟨located,permission.2.1,ih permission.2.2⟩

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

namespace Contracts

theorem DropContract.normal_borrow_returned {program : Kernel.Program} {host : Foreign.Model}
    {self region : Term} {function : Kernel.Function} {observation : Observation}
    {result : Address} {input : Kernel.InvocationInput} {value : Value} {id : Identity} {original : Loan}
    (contract : DropContract program self region function) (lawful : host.Lawful program)
    (observed : Observes program host function observation) (normal : observation.outcome = .normal result)
    (member : input ∈ observation.input) (stored : observation.before.Stores input.storage value)
    (head : value.head = .reference id) (loan : observation.before.loans.get id = some original) :
    DropBorrowReturned self observation.after id original :=
  contract.2.2.1 host observation lawful observed result normal input member value id original stored head loan

end Contracts

namespace Execution

/-- The finite administrative suffix at a returned hook. The result and handle
are actual private roots, not a promise that arbitrary user destructor code
terminates. Receiver authority is framed if the caller retained it; ending an
unreferenced parent is not silently interpreted as permission on a dead loan. -/
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
    (resultFound : before.world.root result = some resultRoot) (resultWhole : result.fields = [])
    (unitValue : resultRoot.value = some (.resident unitOwner .unit .unit true []))
    (resultPrivate : CanEndStorage before.world result.root)
    (separate : result.root ≠ address.root)
    (handleFound : before.world.roots.get handle.root = some handleRoot)
    (handleLive : handleRoot.live = true) (handleVacant : handleRoot.value = none)
    (handlePrivate : CanEndStorage before.world handle.root) :
    ∃ after,
      Run program host before [.destroy result unitOwner,.retire result.root,.retire handle.root] after ∧
      after.task = .destroyFields outer address authority (List.range receiver.fields.length).reverse next ∧
      after.frames = rest ∧ after.world.Stores address receiver ∧
      after.world.loans = before.world.loans ∧
      after.world.loans.get loan = some { original with live := false } ∧
      (∀ permission access, Permitted before.world permission access address → Permitted after.world permission access address) ∧
      Typing.WorldTyped program after.world ∧
      (∃ event following, LocalStep program after event following) := by
  have ⟨resultAt,resultLive,resultGeneration⟩ := World.root_found resultFound
  have different : handle.root ≠ result.root := by
    intro same
    have equal := Option.some.inj (handleFound.symm.trans (same ▸ resultAt))
    have impossible := handleVacant.symm.trans (equal ▸ unitValue)
    cases impossible
  let cleared : World := { before.world with roots := before.world.roots.set result.root { resultRoot with value := none } }
  let resultRetired : World := { cleared with roots := cleared.roots.set result.root { resultRoot with value := none,live := false,generation := resultRoot.generation+1 } }
  let afterWorld : World := { resultRetired with roots := resultRetired.roots.set handle.root { handleRoot with live := false,generation := handleRoot.generation+1 } }
  have written : before.world.write result none = some cleared := by
    simp [World.write,resultFound,resultWhole,cleared]
  have clearResult : cleared.roots.get result.root = some { resultRoot with value := none } := Table.get_set _ _ _
  have retireResult : Retires cleared result.root resultRetired :=
    .vacant clearResult resultLive rfl (World.write_canEndStorage written resultPrivate)
  have retireHandle : Retires resultRetired handle.root afterWorld := by
    have retained : resultRetired.roots.get handle.root = some handleRoot := by
      simpa only [resultRetired,cleared,Table.get_set_other _ _ _ _ different] using handleFound
    have safe : CanEndStorage resultRetired handle.root := by
      apply handlePrivate.sameHomes (after := resultRetired) ?_ rfl rfl
      simp only [resultRetired,cleared,Table.get_set_other _ _ _ _ different]
    exact .vacant retained handleLive handleVacant safe
  have unitStored : before.world.Stores result (.resident unitOwner .unit .unit true []) := by
    simp [World.Stores,World.read,resultFound,unitValue,resultWhole,Value.atPath]
  have unitPermission : Permitted before.world .owner .owned result := by
    have permission := resultPrivate.owner_permission resultAt resultLive
    have shape : (⟨result.root,resultRoot.generation,[]⟩ : Address) = result := by
      cases result
      simp_all
    exact shape ▸ permission
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
  let vacant := { shell with world := cleared,task := retireR }
  let endedResult := { vacant with world := resultRetired,task := retireH }
  let endedHandle := { endedResult with world := afterWorld,task := close }
  let after := { endedHandle with task := fields }
  have start : LocalStep program before none started := .hookReturned task frames stored
  have noDrop : DropHook program.declarations .unit none := by
    refine Or.inr ⟨?_,rfl⟩
    intro id args impossible
    cases impossible
  have structuralStep : LocalStep program started none structural := by
    have step := LocalStep.destroyStructural (program := program) (before := started) rfl unitStored
      unitDisposable unitPermission (Or.inr noDrop)
      (by intro id impossible; cases impossible) (by intro id impossible; cases impossible)
      (by intro id impossible; cases impossible)
    exact step
  have fieldStep : LocalStep program structural none shell := .fieldsDone rfl
  have shellStep : LocalStep program shell (some (.destroy result unitOwner)) vacant :=
    .shellDone (before := shell) rfl unitStored (by simp [Value.fields]) unitPermission written
  have resultStep : LocalStep program vacant (some (.retire result.root)) endedResult := .retire rfl retireResult
  have handleStep : LocalStep program endedResult (some (.retire handle.root)) endedHandle := .retire rfl retireHandle
  have loanStep : LocalStep program endedHandle none after := .loanAlreadyEnded rfl ended rfl
  have cleanup : CleanupRun program host started [.destroy result unitOwner,.retire result.root,.retire handle.root] after := by
    exact .silent trivial (Or.inl structuralStep)
      (.silent trivial (Or.inl fieldStep)
        (.visible trivial (Or.inl shellStep)
          (.visible trivial (Or.inl resultStep)
            (.visible trivial (Or.inl handleStep)
              (.silent trivial (Or.inl loanStep) .refl)))))
  have retained : after.world.Stores address receiver := by
    exact (retireHandle.read address).trans ((retireResult.read address).trans
      ((World.write_disjoint written (fun overlap => separate overlap.1)).trans stored))
  have located : ∃ root, after.world.root address = some root :=
    (Option.bind_eq_some_iff.mp retained).imp fun _ found => found.1
  refine ⟨after,.silent (Or.inl start) cleanup.run,rfl,rfl,retained,rfl,ended,?_,?_,?_⟩
  · exact fun _ _ permission => permission.sameLoansAt (before := before.world) (after := after.world) rfl located
  · exact cleanup.worldTyped (before := started) valid inventory typed
  · cases selected : (List.range receiver.fields.length).reverse with
    | nil => exact ⟨none,_,.fieldsDone (context := outer) (address := address) (authority := authority)
        (next := next) (by change fields = _; simp [fields,selected])⟩
    | cons field remaining => exact ⟨none,_,.fieldNext (context := outer) (address := address) (authority := authority)
        (field := field) (fields := remaining) (next := next) (by change fields = _; simp [fields,selected])⟩

end Execution

namespace Contracts

/-- Composition of the checked application, actual normal observation and
ordinary returned-hook suffix. Initial storage typing comes from the observed
invocation and preservation, not an assumed post-world. Private result and
vacant-handle provenance are the remaining caller-frame inputs; no standalone
observation theorem is misrepresented as a general stack-embedding proof. -/
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
    (world : before.world = observation.after) (task : before.task = .yield context result)
    (frames : before.frames = .hook outer original.referent authority input.storage loan next :: rest)
    (resultFound : before.world.root result = some resultRoot) (resultWhole : result.fields = [])
    (unitValue : resultRoot.value = some (.resident unitOwner .unit .unit true []))
    (resultPrivate : CanEndStorage before.world result.root)
    (handleFound : before.world.roots.get input.storage.root = some handleRoot)
    (handleLive : handleRoot.live = true) (handleVacant : handleRoot.value = none)
    (handlePrivate : CanEndStorage before.world input.storage.root) :
    ∃ receiver after,
      observation.after.Stores original.referent receiver ∧ receiver.type = self ∧ receiver.Initialized ∧
      MayDispose program.declarations receiver ∧
      Execution.Run program host before [.destroy result unitOwner,.retire result.root,.retire input.storage.root] after ∧
      after.task = .destroyFields outer original.referent authority (List.range receiver.fields.length).reverse next ∧
      after.frames = rest ∧ after.world.Stores original.referent receiver ∧
      DropBorrowReturned self after.world loan original ∧
      (∀ permission access, Permitted observation.after permission access original.referent →
        Permitted after.world permission access original.referent) ∧
      Typing.WorldTyped program after.world ∧
      (∃ event following, Execution.LocalStep program after event following) := by
  have returned := contract.normal_borrow_returned lawful observed normal member inputStored head selected
  rw [← world] at returned
  obtain ⟨ended,receiver,stored,receiverType,initialized⟩ := returned
  have typed : Typing.WorldTyped program before.world := world ▸ (observed.worldTyped valid.declarations valid.inventory lawful).2
  obtain ⟨principal,capability,discard⟩ := application.capability
  have disposable := (typed.2.1 _ _ (World.resident_iff_stores.mpr stored)).mayDispose valid.inventory initialized
    (receiverType.symm ▸ capability) discard
  have nonunit : receiver.type ≠ .unit := by
    cases application with
    | selected drops _ _ _ _ _ _ _ _ _ =>
      rcases drops with ⟨id,args,data,nominal,_,_⟩ | ⟨_,impossible⟩
      · rw [receiverType,nominal]
        intro impossible
        cases impossible
      · cases impossible
  obtain ⟨after,run,fields,afterFrames,retained,_,loanEnded,permissions,afterTyped,progress⟩ :=
    Execution.hookReturned_administrative valid.declarations valid.inventory typed task frames stored ended
      resultFound resultWhole unitValue resultPrivate (World.stores_outside_unit resultFound unitValue stored nonunit)
      handleFound handleLive handleVacant handlePrivate
  exact ⟨receiver,after,world ▸ stored,receiverType,initialized,disposable,run,fields,afterFrames,retained,
    ⟨loanEnded,receiver,retained,receiverType,initialized⟩,by simpa only [world] using permissions,afterTyped,progress⟩

end Contracts
end Glorious.Language
