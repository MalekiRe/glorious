import GloriousLanguage.ReceiverPreservation
import GloriousLanguage.CleanupPreservation
import GloriousLanguage.StorageFraming
import GloriousLanguage.InvocationLending
import GloriousLanguage.CapabilityModels

/-! Invocation lease cleanup uses the actual reference destruction and
releaseLoan machine path. Parent release is deferred and revisited after a
child ends; allocation ordering is not a second loan-cleanup algorithm. -/
namespace Glorious.Language

/-- A release can reach only unreferenced ancestors with no live children off
the released branch. The optional erased identity is the fieldless handle
about to be destroyed. Deferred parents and unrelated unique holes impose no
restoration obligation. This is a proof view of the actual release guards. -/
def World.InitializedAncestors (world : World) (released : Identity) (erased : Option Identity := none) : Prop :=
  ∀ id loan, AncestorLoan world id released → world.loans.get id = some loan →
    loan.live = true → (erased = some id ∨ ¬ world.References id) →
    (∀ child descendant, world.loans.get child = some descendant → descendant.parent = some id →
      descendant.live = true → AncestorLoan world child released) → world.Initialized loan.referent

/-- Proof view of a release cascade: only loan liveness changes, and every
remaining live loan is an unchanged pre-existing authority. -/
def World.LoanReleaseFrame (before after : World) : Prop :=
  after = { before with loans := after.loans } ∧
  ∀ id loan, after.loans.get id = some loan → loan.live = true → before.loans.get id = some loan

theorem World.LoanReleaseFrame.refl (world : World) : world.LoanReleaseFrame world :=
  ⟨rfl,fun _ _ found _ => found⟩

theorem World.LoanReleaseFrame.trans {before middle after : World}
    (first : before.LoanReleaseFrame middle) (last : middle.LoanReleaseFrame after) :
    before.LoanReleaseFrame after := by
  refine ⟨?_,fun _ _ found live => first.2 _ _ (last.2 _ _ found live) live⟩
  calc
    after = { middle with loans := after.loans } := last.1
    _ = { before with loans := after.loans } := by rw [first.1]

theorem EndsLoan.releaseFrame {before after : World} {id : Identity}
    (ended : EndsLoan before id after) : before.LoanReleaseFrame after := by
  refine ⟨?_,fun _ _ found live => ended.live_origin found live⟩
  cases ended
  rfl

theorem AncestorLoan.beforeEndLoan {before after : World} {endedId ancestor child : Identity}
    (ended : EndsLoan before endedId after) (related : AncestorLoan after ancestor child) :
    AncestorLoan before ancestor child := by
  cases ended with
  | restored selected _ _ _ _ =>
    induction related with
    | refl => exact .refl
    | @parent parent child loan found link _ ih =>
      by_cases changed : child = endedId
      · subst child
        simp only [Table.get_set] at found
        cases found
        exact .parent selected link ih
      · exact .parent (by simpa only [Table.get_set_other _ _ _ _ changed] using found) link ih

theorem EndsLoan.loan_other {before after : World} {id key : Identity} {loan : Loan}
    (ended : EndsLoan before id after) (different : key ≠ id) (found : before.loans.get key = some loan) :
    after.loans.get key = some loan := by
  cases ended
  simpa only [Table.get_set_other _ _ _ _ different] using found

theorem EndsLoan.initializedAncestors {before after : World} {id released : Identity} {erased : Option Identity}
    (initialized : before.InitializedAncestors released erased) (ended : EndsLoan before id after)
    (branch : AncestorLoan before id released) :
    after.InitializedAncestors released erased := by
  intro key loan related found live eligible children
  have original := ended.live_origin found live
  have oldEligible : erased = some key ∨ ¬ before.References key := by cases ended; exact eligible
  have oldChildren : ∀ child descendant, before.loans.get child = some descendant → descendant.parent = some key →
      descendant.live = true → AncestorLoan before child released := by
    intro child descendant selected parent active
    by_cases changed : child = id
    · exact changed ▸ branch
    · exact (children child descendant (ended.loan_other changed selected) parent active).beforeEndLoan ended
  have restored := initialized key loan (related.beforeEndLoan ended) original live oldEligible oldChildren
  cases ended
  exact restored

theorem AncestorLoan.sameLoans {before after : World} {ancestor child : Identity}
    (same : before.loans = after.loans) (related : AncestorLoan before ancestor child) :
    AncestorLoan after ancestor child := by
  induction related with
  | refl => exact .refl
  | parent found link _ ih => exact .parent (same ▸ found) link ih

theorem World.write_initializedAncestors {before after : World} {address : Address} {value : Option Value} {released : Identity}
    (initialized : before.InitializedAncestors released (some released))
    (retained : ∀ key, key ≠ released → before.References key → after.References key)
    (permission : Permitted before .owner .owned address)
    (written : before.write address value = some after) : after.InitializedAncestors released := by
  intro id loan related found live eligible children
  have same : after.loans = before.loans := by
    have framed := congrArg World.loans (World.write_rest written)
    exact framed
  have old : before.loans.get id = some loan := by
    simpa only [same] using found
  have separate : ¬ address.Overlaps loan.referent :=
    fun overlap => permission.2 id loan old live overlap (Or.inl (by decide))
  have oldEligible : some released = some id ∨ ¬ before.References id := by
    by_cases equal : id = released
    · exact Or.inl (congrArg some equal.symm)
    · exact Or.inr fun reference => eligible.elim (by intro impossible; cases impossible)
        (fun absent => absent (retained id equal reference))
  have oldChildren : ∀ child descendant, before.loans.get child = some descendant → descendant.parent = some id →
      descendant.live = true → AncestorLoan before child released := by
    intro child descendant selected parent active
    exact (children child descendant (same ▸ selected) parent active).sameLoans same
  obtain ⟨resident,stored,valid⟩ := initialized id loan (related.sameLoans same) old live oldEligible oldChildren
  exact ⟨resident,(World.write_disjoint written separate).trans stored,valid⟩

theorem World.LoanReleaseFrame.canEndStorage {before after : World} {id : Identity}
    (frame : before.LoanReleaseFrame after) (safe : CanEndStorage before id) : CanEndStorage after id := by
  refine ⟨fun key loan found live => safe.1 key loan (frame.2 key loan found live) live,?_⟩
  intro key available found active address member
  have old : before.availability.get key = some available := by
    simpa only [congrArg World.availability frame.1] using found
  exact safe.2 key available old active address member

theorem AncestorLoan.live_first_child {world : World} {ancestor descendant : Identity} {last : Loan}
    (parents : world.LoanParents) (related : AncestorLoan world ancestor descendant)
    (found : world.loans.get descendant = some last) (live : last.live = true) :
    ancestor = descendant ∨ ∃ first child, world.loans.get first = some child ∧
      child.parent = some ancestor ∧ child.live = true ∧ AncestorLoan world first descendant := by
  induction related generalizing last with
  | refl => exact Or.inl rfl
  | @parent parent descendant loan selected link _ ih =>
    have same : loan = last := Option.some.inj (selected.symm.trans found)
    subst last
    obtain ⟨parentLoan,parentFound,_,_,_,parentLive⟩ := parents descendant loan parent selected link
    rcases ih parentFound (parentLive live) with rfl | ⟨first,child,firstFound,firstParent,firstLive,ancestry⟩
    · exact Or.inr ⟨descendant,loan,selected,link,live,.refl⟩
    · exact Or.inr ⟨first,child,firstFound,firstParent,firstLive,.parent selected link ancestry⟩

theorem AncestorLoan.leaf_live_eq {world : World} {ancestor descendant : Identity} {last : Loan}
    (parents : world.LoanParents)
    (children : ∀ id loan, world.loans.get id = some loan → loan.parent = some ancestor → loan.live = false)
    (related : AncestorLoan world ancestor descendant)
    (found : world.loans.get descendant = some last) (live : last.live = true) : ancestor = descendant := by
  rcases related.live_first_child parents found live with same | ⟨first,child,selected,parent,active,_⟩
  · exact same
  · have dead := children first child selected parent
    simp [active] at dead

theorem EndsLoan.children_dead {before after : World} {id child : Identity} {loan : Loan}
    (valid : before.WellFormed) (ended : EndsLoan before id after)
    (found : before.loans.get child = some loan) (parent : loan.parent = some id) : loan.live = false := by
  cases ended with
  | restored _ _ _ _ children =>
    exact children loan (by simpa [← World.loanIdentity valid found] using found) parent

/-- A parent cannot finish while a live descendant remains, even through a
multi-level reborrow chain. This follows from the actual EndsLoan premise. -/
theorem EndsLoan.no_live_descendant {before after : World} {id child : Identity} {loan : Loan}
    (valid : before.WellFormed) (ended : EndsLoan before id after)
    (related : AncestorLoan before id child) (different : id ≠ child)
    (found : before.loans.get child = some loan) : loan.live = false := by
  cases active : loan.live with
  | false => rfl
  | true =>
    exact False.elim (different (related.leaf_live_eq (World.loanParents valid)
      (fun _ _ selected parent => ended.children_dead valid selected parent) found active))

/-- When all children have ended, the surviving parent authority can again
access its referent. Still-live siblings therefore prevent premature recovery
of a unique parent's whole receiver. -/
theorem Permitted.live_leaf {world : World} {id : Identity} {loan : Loan} {access : Access}
    (valid : world.WellFormed) (found : world.loans.get id = some loan) (live : loan.live = true)
    (strength : access ≠ .shared → loan.mode = .unique)
    (children : ∀ key child, world.loans.get key = some child → child.parent = some id → child.live = false) :
    Permitted world (.loan id) access loan.referent := by
  obtain ⟨root,located⟩ := Option.isSome_iff_exists.mp
    ((valid.2.2.2.2.2.2.2.2.2.2.2.2.1 id loan found).2.2 live).2
  refine ⟨⟨root,located⟩,loan,found,live,rfl,rfl,⟨[],by simp⟩,strength,?_⟩
  intro key other selected active different overlap conflict
  have unique : loan.mode = .unique ∨ other.mode = .unique := by
    rcases conflict with writes | exclusive
    · exact Or.inl (strength writes)
    · exact Or.inr exclusive
  have comparable := valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 id key loan other found selected live active overlap unique
  rcases comparable with descendant | ancestor
  · exact False.elim (different (descendant.leaf_live_eq (World.loanParents valid) children selected active).symm)
  · exact ancestor

/-- The actual invocation producer installs an ordinary reference resident,
including its fieldless shape and the recorded child loan identity. -/
theorem Kernel.LendsResident.lease_resident {program : Language.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : Kernel.LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) :
    ∃ witness owner mode type, lease = some witness ∧ witness.handle.fields = [] ∧
      after.Stores witness.handle (.resident owner (.reference mode (.runtimeRegion region) type)
        (.reference witness.loan) true []) := by
  cases lent with
  | owned => exact False.elim (borrowed rfl)
  | lent _ _ allocated formed =>
    obtain ⟨_,_,_,_,whole⟩ := allocated.new_root
    cases formed with
    | borrow _ _ _ _ _ _ _ _ _ written =>
      have read := World.write_read_inside written []
      simp only [List.append_nil,Value.atPath] at read
      exact ⟨_,_,_,_,rfl,whole,read⟩

theorem MayDispose.reference {program : Language.Program}
    (owner loan : Identity) (mode : Mutability) (region type : Term) :
    MayDispose program (.resident owner (.reference mode region type) (.reference loan) true []) := by
  intro path value resident
  cases resident with
  | root =>
    constructor
    · intro _
      cases mode with
      | shared => exact ⟨.duplicable,PrincipalOf.shared program region type,by simp [Principal.MayDiscard,Principal.Permits]⟩
      | unique => exact ⟨.affine,PrincipalOf.unique program region type,by simp [Principal.MayDiscard,Principal.Permits]⟩
    · intro hook _
      intro path value resident
      cases resident with
      | root => exact ⟨rfl,by simp [Value.fields]⟩
      | field selected _ => simp [Value.fields] at selected
  | field selected _ => simp [Value.fields] at selected

theorem Typing.ValueTyped.reference_leaf {program : Kernel.Program} {world : World} {value : Value} {id : Identity}
    (typed : Typing.ValueTyped program world value) (reference : value.head = .reference id) : value.fields = [] := by
  cases typed <;> simp_all [Value.head,Value.fields]
  rename_i head _
  simp [Execution.ConstructorHead] at head

theorem ResidentAt.leaf {tree value : Value} {path : List Nat}
    (resident : ResidentAt tree path value) (leaf : tree.fields = []) : value = tree ∧ path = [] := by
  cases resident with
  | root => exact ⟨rfl,rfl⟩
  | field selected _ => simp [leaf] at selected

/-- Clearing a fieldless reference owner cannot remove an ancestor's own
reference handles. Retained parent handles therefore defer release without
requiring their possibly still-borrowed referents to be initialized. -/
theorem World.clear_reference_retained {before after : World} {id loanId : Identity} {root : Root} {value : Value}
    (found : before.roots.get id = some root) (resident : root.value = some value)
    (reference : value.head = .reference loanId) (leaf : value.fields = [])
    (written : before.write ⟨id,root.generation,[]⟩ none = some after) :
    ∀ key, key ≠ loanId → before.References key → after.References key := by
  intro key different ⟨observed,other,present,head⟩
  by_cases same : observed.root = id
  · obtain ⟨selected,tree,selectedAt,live,generation,treeAt,nested⟩ := present
    have equal : selected = root := Option.some.inj (selectedAt.symm.trans (same ▸ found))
    subst selected
    have equal : tree = value := Option.some.inj (treeAt.symm.trans resident)
    subst tree
    have equal := (nested.leaf leaf).1
    subst other
    exact False.elim (different (ValueHead.reference.inj (head.symm.trans reference)))
  · refine ⟨observed,other,World.resident_iff_stores.mpr ?_,head⟩
    exact (World.write_disjoint written (fun overlap => same overlap.1.symm)).trans
      (World.resident_iff_stores.mp present)

namespace Execution

theorem CleanupRun.append {program : Kernel.Program} {host : Foreign.Model} {before middle after : State}
    {first last : List Event} (left : CleanupRun program host before first middle)
    (right : CleanupRun program host middle last after) : CleanupRun program host before (first ++ last) after := by
  induction left with
  | refl => exact right
  | silent task step _ ih => exact .silent task step (ih right)
  | visible task step _ ih => exact .visible task step (ih right)

/-- Reference cleanup terminates its administrative release cascade using
strictly decreasing parent identities. It may correctly retain a loan still
referenced or borrowed; it never ends a parent ahead of a live child. -/
theorem releaseLoan_cleanup {program : Kernel.Program} {host : Foreign.Model} (id : Identity)
    (before : State) (next : Task) (valid : before.world.WellFormed)
    (initialized : before.world.InitializedAncestors id) (existsLoan : ∃ loan, before.world.loans.get id = some loan) :
    ∃ world trace, CleanupRun program host { before with task := .releaseLoan id next } trace
      { before with world := world, task := next } ∧ world.WellFormed ∧ before.world.LoanReleaseFrame world := by
  classical
  induction id using Nat.strongRecOn generalizing before next with
  | ind id ih =>
    obtain ⟨loan,found⟩ := existsLoan
    by_cases live : loan.live = true
    · by_cases referenced : before.world.References id
      · refine ⟨before.world,[],?_,valid,.refl _⟩
        exact .silent trivial (Or.inl (.releaseReferenced rfl referenced)) .refl
      · by_cases childExists : ∃ child, before.world.loans.get child.identity = some child ∧
            child.parent = some id ∧ child.live = true
        · obtain ⟨child,selected,parent,active⟩ := childExists
          refine ⟨before.world,[],?_,valid,.refl _⟩
          exact .silent trivial (Or.inl (.releaseBorrowed rfl referenced selected parent active)) .refl
        · have children : ∀ child, before.world.loans.get child.identity = some child →
              child.parent = some id → child.live = false := by
            intro child selected parent
            cases active : child.live with
            | false => rfl
            | true => exact False.elim (childExists ⟨child,selected,parent,active⟩)
          let endedWorld := { before.world with loans := before.world.loans.set id { loan with live := false } }
          have ended : EndsLoan before.world id endedWorld := .restored found live
            (initialized id loan .refl found live (Or.inr referenced) (by
              intro key child selected parent active
              have dead := children child (by simpa only [← World.loanIdentity valid selected] using selected) parent
              simp [active] at dead)) referenced children
          have endedValid := ended.wellFormed valid
          have endedInitialized := ended.initializedAncestors initialized .refl
          cases parent : loan.parent with
          | none =>
            refine ⟨endedWorld,[.loanEnd id],?_,endedValid,ended.releaseFrame⟩
            exact .visible trivial (Or.inl (.releaseRoot rfl found parent ended)) .refl
          | some parentId =>
            obtain ⟨parentLoan,parentFound,older,_,_,_⟩ := World.loanParents valid id loan parentId found parent
            have stillFound : endedWorld.loans.get parentId = some parentLoan := by
              simpa only [endedWorld,Table.get_set_other _ _ _ _ (Nat.ne_of_lt older)] using parentFound
            have parentInitialized : endedWorld.InitializedAncestors parentId := by
              intro key ancestor related selected active eligible children
              exact endedInitialized key ancestor (.parent (Table.get_set _ _ _) parent related) selected active eligible
                (fun child descendant found parentFound live =>
                  .parent (Table.get_set _ _ _) parent (children child descendant found parentFound live))
            obtain ⟨world,trace,run,well,frame⟩ := ih parentId older { before with world := endedWorld } next
              endedValid parentInitialized ⟨parentLoan,stillFound⟩
            refine ⟨world,.loanEnd id :: trace,?_,well,ended.releaseFrame.trans frame⟩
            exact .visible trivial (Or.inl (.releaseChild rfl found parent ended)) run
    · have dead : loan.live = false := by cases active : loan.live <;> simp_all
      refine ⟨before.world,[],?_,valid,.refl _⟩
      exact .silent trivial (Or.inl (.releaseAlreadyEnded rfl found dead)) .refl

/-- Destroying a lease reference owner uses the ordinary destruction event,
the complete parent-release cascade, then physical root retirement. Its input
is the real referent-restoration and storage-release obligation, not an
assumption that cleanup already terminates or preserves the world. -/
theorem referenceRoot_cleanup {program : Kernel.Program} {host : Foreign.Model}
    (before : State) (context : Context) (next : Task) {id : Identity} {root : Root} {value : Value} {loanId : Identity}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (initialized : before.world.InitializedAncestors loanId (some loanId))
    (found : before.world.roots.get id = some root) (live : root.live = true) (resident : root.value = some value)
    (reference : value.head = .reference loanId) (disposable : MayDispose program.declarations value)
    (safe : CanEndStorage before.world id) :
    ∃ world trace, CleanupRun program host
      { before with task := .destroy context ⟨id,root.generation,[]⟩ .owner (.retire id next) } trace
      { before with world := world, task := next } ∧ Typing.WorldTyped program world ∧
      ∃ retired, world.roots.get id = some retired ∧ retired.live = false := by
  let address : Address := ⟨id,root.generation,[]⟩
  let cleared := { before.world with roots := before.world.roots.set id { root with value := none } }
  have permission := safe.owner_permission found live
  have stored : before.world.Stores address value := by
    simp [address,World.Stores,World.read,World.root,found,live,resident,Value.atPath]
  have written : before.world.write address none = some cleared := by
    simp [address,cleared,World.write,World.root,found,live]
  have clearedTyped := World.clear_worldTyped typed permission written
  have leaf := (typed.2.1 address value (World.resident_iff_stores.mpr stored)).reference_leaf reference
  have clearedInitialized := World.write_initializedAncestors initialized
    (World.clear_reference_retained found resident reference leaf written) permission written
  obtain ⟨loan,selected,_⟩ := typed.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 address value loanId
    (World.resident_iff_stores.mpr stored) reference
  obtain ⟨released,trace,releases,releasedWell,frame⟩ := releaseLoan_cleanup (program := program) (host := host) loanId
    { before with world := cleared } (.retire id next) clearedTyped.1 clearedInitialized ⟨loan,selected⟩
  have releasedRoot : released.roots.get id = some { root with value := none } := by
    simpa only [congrArg World.roots frame.1] using (Table.get_set before.world.roots id { root with value := none })
  have releasedSafe : CanEndStorage released id := frame.canEndStorage safe
  let retiredWorld := { released with roots := released.roots.set id { root with value := none, live := false, generation := root.generation+1 } }
  have retired : Retires released id retiredWorld := .vacant releasedRoot live rfl releasedSafe
  have retireRun : CleanupRun program host { before with world := released, task := .retire id next }
      [.retire id] { before with world := retiredWorld, task := next } :=
    .visible trivial (Or.inl (.retire rfl retired)) .refl
  have run : CleanupRun program host
      { before with task := .destroy context address .owner (.retire id next) }
      (.destroy address value.owner :: (trace ++ [.retire id])) { before with world := retiredWorld, task := next } :=
    .visible trivial (Or.inl (.destroyReference rfl stored reference disposable permission written))
      (releases.append retireRun)
  have finalTyped : Typing.WorldTyped program retiredWorld :=
    CleanupRun.worldTyped (before := { before with task := .destroy context address .owner (.retire id next) })
      (after := { before with world := retiredWorld, task := next }) valid inventory typed run
  exact ⟨retiredWorld,_,run,finalTyped,_,Table.get_set _ _ _,rfl⟩

/-- Activation cleanup selects the real callee-owned handle root and consumes
the reference cleanup result before advancing to the remaining actual roots. -/
theorem activationReference_cleanup {program : Kernel.Program} {host : Foreign.Model}
    (before : State) (context : Context) (next : Task) {id : Identity} {roots kept : List Identity}
    {root : Root} {value : Value} {loanId : Identity}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (initialized : before.world.InitializedAncestors loanId (some loanId))
    (activation : Kernel.ActivationRoots before.world context.activation kept (id :: roots))
    (found : before.world.roots.get id = some root) (resident : root.value = some value)
    (reference : value.head = .reference loanId) (disposable : MayDispose program.declarations value)
    (safe : CanEndStorage before.world id) :
    ∃ world trace, CleanupRun program host { before with task := .cleanup context (id :: roots) next } trace
      { before with world := world, task := .cleanup context roots next } ∧ Typing.WorldTyped program world ∧
      ∃ retired, world.roots.get id = some retired ∧ retired.live = false := by
  obtain ⟨selected,selectedAt,live,_,_⟩ := (activation.2 id).mp (by simp)
  have same : selected = root := Option.some.inj (selectedAt.symm.trans found)
  subst selected
  obtain ⟨world,trace,run,typed,retired⟩ := referenceRoot_cleanup before context (.cleanup context roots next)
    valid inventory typed initialized found live resident reference disposable safe
  exact ⟨world,trace,.silent trivial (Or.inl (.cleanupRoot rfl found live)) run,typed,retired⟩

/-- Physical cleanup consumes the exact handle produced by invocation lending.
No post-cleanup typing or termination premise is supplied: the static
capability equations justify disposal and the existing machine path does the
clearing, ancestor release, and retirement. -/
theorem lendsResident_cleanup {program : Kernel.Program} {host : Foreign.Model}
    (initial : World) (before : State) (context : Context) (next : Task)
    {address : Address} {authority permission : Authority} {access : Access} {lease : Option Kernel.InvocationLease}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (initialTyped : Typing.WorldTyped program initial)
    (lent : Kernel.LendsResident program.declarations context.activation context.scope context.region
      initial address authority access lease permission before.world)
    (borrowed : access ≠ .owned)
    (restored : ∀ witness, lease = some witness → before.world.InitializedAncestors witness.loan (some witness.loan))
    (safe : ∀ witness, lease = some witness → CanEndStorage before.world witness.handle.root) :
    ∃ witness world trace, lease = some witness ∧
      CleanupRun program host
        { before with task := .destroy context witness.handle .owner (.retire witness.handle.root next) } trace
        { before with world := world, task := next } ∧ Typing.WorldTyped program world ∧
      ∃ retired, world.roots.get witness.handle.root = some retired ∧ retired.live = false := by
  have typed := lent.worldTyped valid inventory initialTyped
  obtain ⟨witness,owner,mode,type,selected,whole,stored⟩ := lent.lease_resident borrowed
  obtain ⟨root,tree,found,live,generation,resident,nested⟩ := World.resident_iff_stores.mpr stored
  have rootValue : root.value = some (.resident owner (.reference mode (.runtimeRegion context.region) type)
      (.reference witness.loan) true []) := by
    rw [whole] at nested
    cases nested
    exact resident
  have sameAddress : witness.handle = ⟨witness.handle.root,root.generation,[]⟩ := by
    calc
      witness.handle = ⟨witness.handle.root,witness.handle.generation,witness.handle.fields⟩ := rfl
      _ = _ := by rw [generation,whole]
  obtain ⟨world,trace,run,finalTyped,retired⟩ := referenceRoot_cleanup (host := host) before context next
    valid inventory typed (restored witness selected) found live rootValue rfl
    (MayDispose.reference owner witness.loan mode (.runtimeRegion context.region) type) (safe witness selected)
  refine ⟨witness,world,trace,selected,?_,finalTyped,retired⟩
  simpa only [← sameAddress] using run

end Execution
end Glorious.Language
