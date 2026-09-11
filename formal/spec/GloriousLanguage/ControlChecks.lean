import GloriousLanguage.Typing

namespace Glorious.Language.ControlChecks

open Kernel Execution

private def witnessType : Term := .available (.runtimeBrand (.proof 3)) (.runtimeRegion 4)
private def witness : Value := .resident 8 witnessType (.available 3) true []
private def source : Address := ⟨10,0,[]⟩
private def destination : Address := ⟨11,0,[]⟩
private def home : Root :=
  ⟨.localSlot 1 4,0,4,1,⟨0,1,[],0,0,[]⟩,witnessType,some witness,false,0,true,[]⟩
private def vacant : Root := { home with value := none }
private def world : World :=
  { roots := [(10,home),(11,vacant)]
    availability := [(3,⟨3,.runtimeBrand (.proof 3),4,[],true⟩)]
    nextRoot := 12
    nextOwner := 9
    nextRegion := 5
    nextProof := 4
    liveRegions := [4] }
private def cleared : World := { world with roots := world.roots.set 10 vacant }
private def moved : World := { cleared with roots := cleared.roots.set 11 home }
private def unitWorld : World := { world with roots := world.roots.set 11 { vacant with type := .unit } }
private def context : Execution.Context :=
  { environment := [⟨17,source,.owner⟩]
    module := default
    activation := 1
    scope := 4
    region := 4 }

private theorem initialized : witness.Initialized := by
  intro path resident location
  cases location with
  | root => simp [witness, Value.shellLive, Value.fields]
  | field member _ => simp [witness, Value.fields] at member

private theorem resolved : ResolvesPlace world context.environment ⟨17,[]⟩ source .owner := by
  refine .localSlot (binding := ⟨17,source,.owner⟩) (by simp [context]) rfl ?_ .nil
  intro other member _
  simpa [context] using member

private theorem transferred : Transfers world .owner source destination moved := by
  refine .move (value := witness) (cleared := cleared) rfl initialized ?_ ?_ ?_ rfl rfl
  · refine ⟨⟨home,rfl⟩,?_⟩
    intro id loan found
    simp [world, Table.get] at found
  · exact ⟨vacant,rfl,Or.inl ⟨rfl,rfl⟩⟩
  · simp [source, destination, Address.Overlaps]

/-- Local 17 carries runtime proof 3. Execution moves that exact resident;
the two identity namespaces do not need to have equal numbers. -/
example (program : Kernel.Program) :
    ControlStep program
      { world := world, task := .atom context destination (.available ⟨17,[]⟩) .abort }
      (some (.move source destination))
      { world := moved, task := .run context .abort } :=
  .available rfl resolved rfl rfl transferred

example (program : Kernel.Program) :
    Typing.AtomType program ⟨default,[⟨17,witnessType,false⟩],[],.row [] [],none⟩
      (.available ⟨17,[]⟩) witnessType := by
  exact .available ⟨⟨17,witnessType,false⟩,by simp,rfl,.nil⟩

private theorem missing {address authority} :
    ¬ ResolvesPlace world context.environment ⟨3,[]⟩ address authority := by
  intro resolution
  rcases resolution.binding with ⟨binding,member,same⟩
  simp [context] at member
  subst binding
  cases same

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
      { world := unitWorld, task := .primitive context destination binding [] [source] .abort }
      none
      { world := unitWorld, task := .destroy context source .owner
          (.atom context destination (.constant (.constantTuple [])) .abort) } :=
  .primitiveCloseAvailable rfl selected rfl rfl

example (program : Kernel.Program) (world : World) (context : Execution.Context)
    (call : Invocation) (selected : EnvironmentAccess) (tail : Bool) (event : Option Event) (after : State)
    (present : call.environment = some selected) :
    ¬ LocalStep program { world := world, task := .apply context call tail } event after := by
  intro step
  cases step <;> simp_all

example (context : Execution.Context) (address : Address) (next : Task) :
    DisposesReservations context [⟨address,.loan 7⟩] next = .destroy context address (.loan 7) next := rfl

example {world reserved access formals inputs input}
    (planned : ReservationInputs world reserved access formals inputs) (member : input ∈ inputs) :
    input.access = access := by
  rcases planned with ⟨_,rfl,_⟩
  rcases List.mem_map.mp member with ⟨⟨entry,index⟩,_,rfl⟩
  rfl

example {world : World} (valid : world.WellFormed) :
    world.availability.get world.nextProof = none ∧ world.bindings.get world.nextProof = none := World.freshProof valid

example (world : World) (address : Address) (id : Identity) :
    ConsumesAvailability world address id .shared world := .lent (by decide)

example {before after : World} {address id} (used : ConsumesAvailability before address id .owned after) :
    ∃ available, after.availability.get id = some available ∧ available.active = false := by
  cases used with
  | lent impossible => exact False.elim (impossible rfl)
  | owned _ _ => simp [Table.get, Table.set]

end Glorious.Language.ControlChecks
