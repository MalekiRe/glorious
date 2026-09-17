import GloriousLanguage.Typing

/-! Execution witnesses at the actual control/binding boundary. A lexical
binding key selects the source place, actual resident handoff readiness
authorizes the move, and the selected ledger authority bounds what dispatch
may destroy. Exhaustion retains those same readiness obligations instead of
producing a successor world. These are contract checks, not source admission. -/
namespace Glorious.Language.ControlChecks

open Kernel Execution

private def witnessType : Term := .available (.runtimeBrand (.proof 3)) (.runtimeRegion 4) []
private def witness : Value := .resident 8 witnessType (.available 3) true []
private def source : Address := ⟨10,0,[]⟩
private def destination : Address := ⟨11,0,[]⟩
private def home : Root :=
  ⟨.localSlot 1 4,0,4,1,⟨0,1,[],0,0,[]⟩,witnessType,some witness,false,0,true,[]⟩
private def vacant : Root := { home with value := none }
private def world : World :=
  { roots := [(10,home),(11,vacant)]
    availability := [(3,⟨3,.runtimeBrand (.proof 3),4,[],[],true⟩)]
    nextRoot := 12
    nextOwner := 9
    nextRegion := 5
    nextProof := 4
    liveRegions := [4] }
private def cleared : World := { world with roots := world.roots.set 10 vacant }
private def moved : World := { cleared with roots := cleared.roots.set 11 home }
private def context : Execution.Context :=
  { environment := [⟨.localSlot 17,source,.owner⟩]
    module := default
    activation := 1
    scope := 4
    region := 4 }

private theorem initialized : witness.Initialized := by
  intro path resident location
  cases location with
  | root => simp [witness, Value.shellLive, Value.fields]
  | field member _ => simp [witness, Value.fields] at member

private theorem resident_eq {resident : Value} {path : List Nat}
    (location : ResidentAt witness path resident) : resident = witness := by
  cases location with
  | root => rfl
  | field member _ => simp [witness, Value.fields] at member

/-- The witness retains no reference handle and no erased resource, so its
whole reachable graph is itself. -/
private theorem reachable_eq {state : World} {authority current : Authority} {incoming access : Access}
    {resident : Value}
    (reachable : witness.ReachableResident state authority incoming resident current access) :
    resident = witness := by
  induction reachable with
  | resident location => exact resident_eq location
  | referent _ head _ _ _ ih => simp [ih, witness, Value.head] at head
  | resource _ member _ _ ih => simp [ih, witness, Value.resources] at member

private theorem noReference {state : World} {authority current : Authority} {incoming access : Access}
    {identity : Identity} : ¬ witness.ReachableReference state authority incoming identity current access := by
  rintro ⟨resident,reachable,head⟩
  simp [reachable_eq reachable, witness, Value.head] at head

private theorem noSupport {state : World} {address : Address} : ¬ witness.Support state address := by
  rintro ⟨resident,authority,access,reachable,observed⟩
  rcases observed with ⟨identity,loan,reference,found,referent⟩ | ⟨binding,member,addressEq⟩
  · simp [reachable_eq reachable, witness, Value.head] at reference
  · simp [reachable_eq reachable, witness, Value.resources] at member

private theorem accessible (program : RuntimeProgram) (state : World) (access : Access) :
    witness.ResourcesAccessible program state access := by
  refine ⟨?_,?_,?_,?_⟩
  · intro resident authority incoming reachable
    rw [reachable_eq reachable]
    exact ⟨by simp [witness, Value.resources], rfl⟩
  · intro identity authority incoming reachable
    exact False.elim (noReference reachable)
  · intro identity authority incoming reachable
    exact False.elim (noReference reachable)
  · intro resident authority incoming reachable binding member
    simp [reachable_eq reachable, witness, Value.resources] at member

private theorem ready (program : RuntimeProgram) (state : World) (footprint : List Address) :
    witness.MoveReady program state footprint := by
  refine ⟨accessible program state .owned, ?_⟩
  intro mutation member address supported
  exact False.elim (noSupport supported)

/-- Local 17 carries runtime proof 3. The lexical binding key, not the runtime
proof identity, selects the source place. -/
private theorem resolved : ResolvesPlace world context.environment ⟨17,[]⟩ source .owner := by
  refine .localSlot (binding := ⟨.localSlot 17,source,.owner⟩) ⟨by simp [context],rfl,?_⟩ .nil
  intro other member _
  simpa [context] using member

private theorem transferred (program : RuntimeProgram) :
    Transfers program world .owner source destination moved := by
  refine .move (value := witness) (cleared := cleared) rfl initialized
    (ready program world [source,destination]) ?_
    ⟨vacant,rfl,Or.inl ⟨rfl,rfl⟩⟩ (by simp [source,destination,Address.Overlaps])
    ⟨0,.root (root := vacant) (id := 11) rfl rfl⟩ rfl rfl
  refine ⟨⟨home,rfl⟩,?_⟩
  intro id loan found
  simp [world,Table.get] at found

/-- Execution moves that exact resident; the two identity namespaces do not
need to have equal numbers. -/
example (program : Kernel.Program) :
    ControlStep program
      { world := world, task := .atom context destination (.available ⟨17,[]⟩) .abort }
      (some (.move source destination))
      { world := moved, task := .run context .abort } :=
  .available rfl resolved rfl rfl (transferred _)

example (program : Kernel.Program) :
    Typing.AtomType program ⟨default,[⟨17,witnessType,false⟩],[],.row [] [],none⟩
      (.available ⟨17,[]⟩) witnessType := by
  exact .available ⟨⟨17,witnessType,false⟩,by simp,rfl,.nil⟩

private theorem missing {address authority} :
    ¬ ResolvesPlace world context.environment ⟨3,[]⟩ address authority := by
  intro resolution
  rcases ResolvesPlace.binding resolution with ⟨binding,member,key⟩
  simp [context] at member
  subst binding
  injection key with number
  exact absurd number (by decide)

/-- Knowing a live table key does not supply its witness as a local operand. -/
example (program : Kernel.Program) (event : Option Event) (after : State) :
    ¬ ControlStep program
      { world := world, task := .atom context destination (.available ⟨3,[]⟩) .abort } event after := by
  intro step
  cases step <;> simp_all
  obtain ⟨rfl,rfl,rfl,rfl⟩ := (by assumption :
    context = _ ∧ destination = _ ∧ (⟨3,[]⟩ : Place) = _ ∧ Code.abort = _)
  exact missing (by assumption)

example (program : Kernel.Program) (event : Option Event) (after : State) :
    ¬ ControlStep program
      { world := world, task := .atom context destination (.bindings ⟨3,[]⟩) .abort } event after := by
  intro step
  cases step <;> simp_all
  obtain ⟨rfl,rfl,rfl,rfl⟩ := (by assumption :
    context = _ ∧ destination = _ ∧ (⟨3,[]⟩ : Place) = _ ∧ Code.abort = _)
  exact missing (by assumption)

example (program : Kernel.Program) (binding : RuntimeBinding)
    (selected : binding.primitive = some .availableClose) :
    ControlStep program
      { world := world, task := .primitive context destination binding [] [⟨source,.owner⟩] .abort }
      none
      { world := world, task := .destroy context source .owner
          (.atom context destination (.constant (.constantTuple [])) .abort) } :=
  .primitiveCloseAvailable (source := ⟨source,.owner⟩) (value := witness)
    (before := { world := world, task := .primitive context destination binding [] [⟨source,.owner⟩] .abort })
    rfl selected rfl rfl

/-- Dispatch may schedule cleanup through a lent view, but must not turn it
into owner authority. The shared view consequently cannot execute destruction. -/
example (program : Kernel.Program) (binding : RuntimeBinding) (backing : Authority)
    (selected : binding.primitive = some .availableClose) :
    ControlStep program
      { world := world, task := .primitive context destination binding [] [⟨source,.shared backing⟩] .abort }
      none
      { world := world, task := .destroy context source (.shared backing)
          (.atom context destination (.constant (.constantTuple [])) .abort) } :=
  .primitiveCloseAvailable (source := ⟨source,.shared backing⟩) (value := witness)
    (before := { world := world, task := .primitive context destination binding [] [⟨source,.shared backing⟩] .abort })
    rfl selected rfl rfl

/-- The ordered handoff has two exclusive outcomes: a protected successor
comes from a fresh allocation, while an exhausted attempt is returned with
its own readiness and permission obligation intact. -/
example {program : Kernel.Program} {context : Execution.Context} {before : World}
    {_source address : Address} {authority : Authority}
    (exhausted : ProtectExhausted program context before address authority) :
    ∃ value, before.Stores address value ∧ value.Initialized ∧
      value.MoveReady program before [address] ∧ Permitted before authority .owned address := by
  obtain ⟨value,layout,stored,initialized,ready,permitted,request⟩ := exhausted
  exact ⟨value,stored,initialized,ready,permitted⟩

example (program : Kernel.Program) (world : World) (context : Execution.Context)
    (call : Invocation) (selected : EnvironmentAccess) (tail : Bool) (event : Option Event) (after : State)
    (present : call.environment = some selected) :
    ¬ LocalStep program { world := world, task := .apply context call tail } event after := by
  intro step
  cases step <;> simp_all

example (context : Execution.Context) (address : Address) (next : Task) :
    DisposesReservations context [⟨address,.loan 7⟩] next = .destroy context address (.loan 7) next := rfl

/-- Every reserved input keeps the selected access, including erased ports
whose storage is a real initialized resident of the declared type. -/
example {world available access formals inputs input}
    (planned : ReservationInputs world available access formals inputs) (member : input ∈ inputs) :
    input.access = access := by
  have expanded := planned.2.2.1
  rw [expanded] at member
  rcases List.mem_map.mp member with ⟨⟨entry,index⟩,_,rfl⟩
  rfl

example {world : World} (valid : world.WellFormed) :
    world.availability.get world.nextProof = none ∧
    ∀ address value pack, world.Resident address value → value.head = .bindings pack → pack.brand ≠ world.nextProof :=
  World.freshProof valid

example (world : World) (address : Address) (authority : Authority) (id : Identity) :
    ConsumesAvailability world address authority id .shared world := .lent (by decide)

example {before after : World} {address authority id}
    (used : ConsumesAvailability before address authority id .owned after) :
    ∃ available, after.availability.get id = some available ∧ available.active = false := by
  cases used with
  | lent impossible => exact False.elim (impossible rfl)
  | owned _ _ _ _ _ _ _ => exact ⟨_, Table.get_set _ _ _, rfl⟩

end Glorious.Language.ControlChecks
