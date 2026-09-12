import GloriousLanguage.ConstructionPreservation
import GloriousLanguage.LocalPreservation

/-! Sealed reservation publication and contextual invocation consume the same
frozen storage/type ledger. Proof-only reordering below establishes atomic
publication from the actual write, not an admissible post-state premise. -/
namespace Glorious.Language

/-- A record-update abbreviation used to prove that publishing proof metadata
commutes with storage construction. It does not execute a second traversal. -/
def World.withProofs (world : World) (proofs : Table Availability) (next : Identity) : World :=
  { world with availability := proofs, nextProof := next }

theorem World.write_withProofs (before : World) (proofs : Table Availability) (next : Identity)
    (address : Address) (replacement : Option Value) :
    (before.withProofs proofs next).write address replacement =
      (before.write address replacement).map (fun world => world.withProofs proofs next) := by
  unfold World.write
  change (before.root address).bind _ = ((before.root address).bind _).map _
  cases selected : before.root address with
  | none => rfl
  | some root =>
      dsimp
      split
      · rfl
      · cases present : root.value with
        | none => rfl
        | some value =>
            dsimp
            cases value.replace address.fields replacement <;> rfl

theorem Clears.withProofs {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) (proofs : Table Availability) (next : Identity) :
    Clears (before.withProofs proofs next) addresses (after.withProofs proofs next) := by
  induction cleared with
  | nil => exact .nil
  | cons written _ ih =>
      exact .cons (by rw [World.write_withProofs,written]; rfl) ih

theorem NewValue.withProofs {program : Program} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after)
    (proofs : Table Availability) (next : Identity) :
    NewValue program (before.withProofs proofs next) destination type head sources (after.withProofs proofs next) := by
  cases constructed with
  | construct vacant located inputs initialized separate permissions cleared written =>
      rename_i residents taken middle
      refine .construct (before := before.withProofs proofs next) (head := head)
        (after := middle.withProofs proofs next)
        vacant (located.retained (fun _ selected => selected) (fun _ => rfl))
        inputs initialized separate ?_ (cleared.withProofs proofs next) ?_
      · intro source member
        exact ⟨(permissions source member).1.transport (before := before)
          (after := before.withProofs proofs next) (fun _ => rfl) rfl,(permissions source member).2⟩
      · rw [World.write_withProofs]
        dsimp only [World.withProofs]
        rw [written]
        rfl

theorem Typing.ValueTyped.extendProofs {program : Kernel.Program} {world : World} {value : Value}
    {proofs : Table Availability} {next : Identity}
    (retained : ∀ id available, world.availability.get id = some available → proofs.get id = some available)
    (typed : Typing.ValueTyped program world value) :
    Typing.ValueTyped program (world.withProofs proofs next) value := by
  refine Typing.ValueTyped.rec
    (motive_1 := fun value _ => Typing.ValueTyped program (world.withProofs proofs next) value)
    (motive_2 := fun fields types _ => Typing.FieldsTyped program (world.withProofs proofs next) fields types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · exact fun {_ _} => .unit
  · exact fun {_ _ _} valid => .scalar valid
  · exact fun {_ _ _ _ _ _} shape _ fields => .aggregate shape fields
  · exact fun {_ _ _ _ _ _ _} found active mode region located =>
      .reference found active mode region (located.retained (fun _ found => found) (fun _ => rfl))
  · exact fun {_ _ _ _ _} bound origin => .pointer bound origin
  · exact fun {_ _ _ _ _ _} callable _ fields => .callable callable fields
  · exact fun {_ _ _ _ _ _} operation => .operation operation
  · exact fun {_ _ _ _ _} => .label
  · exact fun {_ _ _ _} type => .continuation type
  · exact fun {_ _ _ _ _ _ _} found brand id region residents =>
      .available (retained _ _ found) brand id region residents
  · exact fun {_ _ _ _ _ _ _} _ brand region length distinct fields => .bindings fields brand region length distinct
  · exact .nil
  · exact fun {_ _ _} _ fields => .hole fields
  · exact fun {_ _ _ _} _ type _ value fields => .resident value type fields

theorem World.registerAvailability_wellFormed {world : World} {available : Availability}
    (valid : world.WellFormed) (identity : available.identity = world.nextProof)
    (brand : available.brand = .runtimeBrand (.proof world.nextProof))
    (region : available.region ∈ world.liveRegions)
    (reserved : ∀ place ∈ available.reserved, (world.root place.address).isSome = true) :
    (world.withProofs (world.availability.set world.nextProof available) (world.nextProof+1)).WellFormed := by
  rcases valid with ⟨rootsUnique,loansUnique,proofsUnique,regionsUnique,proofs,packs,owners,unique,
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations⟩
  refine ⟨rootsUnique,loansUnique,proofsUnique.set _ _,regionsUnique,?_,?_,owners,unique,
    roots,regions,bases,ranges,loans,references,?_,parents,locations⟩
  · intro id proof found
    by_cases same : id = world.nextProof
    · subst id
      simp only [World.withProofs,Table.get_set] at found
      cases found
      exact ⟨identity.symm,Nat.lt_succ_self _,brand,fun _ => ⟨region,reserved⟩⟩
    · obtain ⟨oldIdentity,bound,oldBrand,active⟩ := proofs id proof
        (by simpa only [World.withProofs,Table.get_set_other _ _ _ _ same] using found)
      exact ⟨oldIdentity,Nat.lt_succ_of_lt bound,oldBrand,active⟩
  · intro address value pack resident head
    obtain ⟨bound,live,length,distinct,facts⟩ := packs address value pack resident head
    exact ⟨Nat.lt_succ_of_lt bound,live,length,distinct,facts⟩
  · intro a b left right first second leftLive rightLive overlap unique
    exact (overlaps a b left right first second leftLive rightLive overlap unique).imp
      (fun related => related.transport (before := world) rfl)
      (fun related => related.transport (before := world) rfl)

theorem World.registerAvailability_worldTyped {program : Kernel.Program} {world : World} {available : Availability}
    (typed : Typing.WorldTyped program world) (identity : available.identity = world.nextProof)
    (brand : available.brand = .runtimeBrand (.proof world.nextProof))
    (region : available.region ∈ world.liveRegions)
    (reserved : ∀ place ∈ available.reserved, (world.root place.address).isSome = true) :
    Typing.WorldTyped program (world.withProofs (world.availability.set world.nextProof available) (world.nextProof+1)) := by
  refine ⟨World.registerAvailability_wellFormed typed.1 identity brand region reserved,?_,typed.2.2⟩
  intro address value resident
  apply (typed.2.1 address value resident).extendProofs
  intro id proof found
  have different : id ≠ world.nextProof := by
    intro same
    subst id
    rw [(World.freshProof typed.1).1] at found
    cases found
  simpa only [Table.get_set_other _ _ _ _ different] using found

namespace Execution

theorem _root_.Glorious.Language.Permitted.root {world : World} {authority : Authority} {access : Access} {address : Address}
    (allowed : Permitted world authority access address) : ∃ root, world.root address = some root := by
  cases authority <;> exact allowed.1

theorem ResolvedOperands.permitted {world : World} {environment : Kernel.Environment}
    {places : List Kernel.Place} {sources : List ResolvedPlace}
    (resolved : ResolvedOperands world environment places sources) :
    ∀ source ∈ sources, Permitted world source.authority .shared source.address := by
  induction resolved with
  | nil => intro source member; cases member
  | cons current _ ih =>
      intro source member
      rcases List.mem_cons.mp member with rfl | member
      · exact current.2
      · exact ih source member

/-- Atomic publication of the new witness and its frozen ledger. The proof
commutes the actual storage constructor with the metadata update; it does not
ask for a typed unpublished witness or a well-formed output. -/
theorem reserve_worldTyped {program : Kernel.Program} {before allocated after : World}
    {home : Home} {region : Identity} {layout : Layout} {mutable : Bool} {destination : Address}
    {reserved : List ResolvedPlace} {types : List Term}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (allocation : Allocates program.declarations before home region
      (.available (.runtimeBrand (.proof before.nextProof)) (.runtimeRegion region) types)
      layout mutable destination allocated)
    (rooted : ∀ place ∈ reserved, (before.root place.address).isSome = true)
    (created : NewValue program.declarations allocated destination
      (.available (.runtimeBrand (.proof before.nextProof)) (.runtimeRegion region) types)
      (.available before.nextProof) [] after) :
    Typing.WorldTyped program { after with
      nextProof := before.nextProof+1
      availability := after.availability.set before.nextProof
        ⟨before.nextProof,.runtimeBrand (.proof before.nextProof),region,reserved,types,true⟩ } := by
  let available : Availability :=
    ⟨before.nextProof,.runtimeBrand (.proof before.nextProof),region,reserved,types,true⟩
  have proofBase : allocated.nextProof = before.nextProof := by cases allocation; rfl
  have regionLive : region ∈ allocated.liveRegions := by
    cases allocation with
    | fresh live _ _ _ _ _ _ _ _ => exact live
  have allocatedRoots : ∀ place ∈ reserved, (allocated.root place.address).isSome = true := by
    intro place member
    obtain ⟨root,found⟩ := Option.isSome_iff_exists.mp (rooted place member)
    exact Option.isSome_iff_exists.mpr ⟨root,allocation.root typed.1 found⟩
  have registered : Typing.WorldTyped program
      (allocated.withProofs (allocated.availability.set before.nextProof available) (before.nextProof+1)) := by
    have prepared := World.registerAvailability_worldTyped (available := available) (allocation.worldTyped typed)
      proofBase.symm (congrArg (fun id => Term.runtimeBrand (.proof id)) proofBase.symm) regionLive allocatedRoots
    simpa only [proofBase] using prepared
  have made := (created.withProofs (allocated.availability.set before.nextProof available) (before.nextProof+1)).empty_worldTyped
    valid inventory registered (by intro id impossible; cases impossible) (by intro pack impossible; cases impossible)
    (.available (Table.get_set _ _ _) rfl rfl rfl rfl)
  have proofs := congrArg World.availability created.rest
  simpa only [World.withProofs,available,proofs] using made

theorem ConsumesReceiver.locations {before after : World} {address authority access}
    (consumed : ConsumesReceiver before address authority access after) :
    ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  cases consumed with
  | lent => intro; rfl
  | owned _ _ _ _ written => exact World.write_locations written

theorem ConsumesReceiver.loans {before after : World} {address authority access}
    (consumed : ConsumesReceiver before address authority access after) : after.loans = before.loans := by
  cases consumed with
  | lent => rfl
  | owned _ _ _ _ written => exact World.write_loans written

theorem ConsumesAvailability.worldTyped {program : Kernel.Program} {before after : World}
    {address : Address} {id : Identity} {authority : Authority} {access : Access}
    (typed : Typing.WorldTyped program before)
    (permission : access = .owned → Permitted before authority .owned address)
    (consumed : ConsumesAvailability before address id access after) : Typing.WorldTyped program after := by
  cases consumed with
  | lent => exact typed
  | owned found written =>
      apply World.deactivateAvailability_worldTyped (World.clear_worldTyped typed (permission rfl) written)
      have proofs := congrArg World.availability (World.write_rest written)
      simpa only [proofs] using found

/-- Test construction has an additional atomic binding-pack/carrier
publication obligation. All other control steps, including the entire
reservation cycle and contextual call entry, are covered here. -/
def Task.ConstructsTest : Task → Prop
  | .run _ (.test ..) => True
  | _ => False

theorem ControlStep.nonTest_worldTyped {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (step : ControlStep program before event after)
    (notTest : ¬ before.task.ConstructsTest) : Typing.WorldTyped program after.world := by
  cases step <;> try exact typed
  case leave => apply Protect.worldTyped valid inventory typed; assumption
  case reserve resolved types distinct disjoint exclusive typeEq allocation created =>
    rw [typeEq] at allocation created
    apply reserve_worldTyped valid inventory typed allocation ?_ created
    intro place member
    have allowed := resolved.permitted place member
    obtain ⟨root,found⟩ := allowed.root
    exact Option.isSome_iff_exists.mpr ⟨root,found⟩
  case available moved => exact moved.worldTyped valid inventory typed
  case destroyAvailable =>
    apply World.deactivateAvailability_worldTyped
    · apply World.clear_worldTyped typed <;> assumption
    · have written := by assumption
      have proofs := congrArg World.availability (World.write_rest written)
      simpa only [proofs] using (by assumption)
  case destroySpentAvailable => apply World.clear_worldTyped typed <;> assumption
  case contextualCall consumed used =>
    apply used.worldTyped (consumed.worldTyped typed)
    intro access
    apply Permitted.transport consumed.locations consumed.loans
    rw [← access]
    assumption
  case positiveTest => simp_all [Task.ConstructsTest]
  case negativeTest => simp_all [Task.ConstructsTest]
  case bindings moved => exact moved.worldTyped valid inventory typed

end Execution
end Glorious.Language
