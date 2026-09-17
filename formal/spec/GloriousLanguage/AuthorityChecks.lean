import GloriousLanguage.InvocationLending

/-! Positive and negative witnesses at the resolved-operand/ownership handoff
boundary. These do not assume whole-source semantic admission. -/
namespace Glorious.Language.AuthorityChecks

open Kernel Execution Memory

private def source : Address := ⟨0,0,[]⟩
private def destination : Address := ⟨1,0,[]⟩
private def unitValue : Value := .resident 0 .unit .unit true []
private def root : Root :=
  ⟨.localSlot 0 0,0,0,1,⟨0,1,[],0,0,[]⟩,.unit,some unitValue,true,0,true,[]⟩
private def emptyRoot : Root := { root with type := .tuple [.unit], value := none }
private def world : World :=
  { roots := [(0,root),(1,emptyRoot)], liveRegions := [0], nextRoot := 2,
    nextOwner := 1, nextRegion := 1, clock := 1 }
private def context : Execution.Context :=
  { environment := [⟨.localSlot 7,source,.shared .owner⟩], module := default,
    activation := 0, scope := 0, region := 0 }

private theorem initialized : unitValue.Initialized := by
  intro path resident location
  cases location with
  | root => simp [unitValue, Value.shellLive, Value.fields]
  | field member _ => simp [unitValue, Value.fields] at member

private theorem unitResident {resident : Value} {path : List Nat}
    (location : ResidentAt unitValue path resident) : resident = unitValue := by
  cases location with
  | root => rfl
  | field member _ => simp [unitValue,Value.fields] at member

private theorem unitReachable {state : World} {authority current : Authority} {incoming access : Access}
    {resident : Value} (reachable : unitValue.ReachableResident state authority incoming resident current access) :
    resident = unitValue := by
  induction reachable with
  | resident location => exact unitResident location
  | referent _ head _ _ _ ih => simp [ih,unitValue,Value.head] at head
  | resource _ member _ _ ih => simp [ih,unitValue,Value.resources] at member

private theorem unitNoReference {state : World} {authority current : Authority} {incoming access : Access}
    {identity : Identity} : ¬ unitValue.ReachableReference state authority incoming identity current access := by
  rintro ⟨resident,reachable,head⟩
  simp [unitReachable reachable,unitValue,Value.head] at head

private theorem unitReady (program : RuntimeProgram) (state : World) (footprint : List Address) :
    unitValue.MoveReady program state footprint := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro resident authority incoming reachable
    rw [unitReachable reachable]
    exact ⟨by simp [unitValue,Value.resources],rfl⟩
  · intro identity authority incoming reachable
    exact False.elim (unitNoReference reachable)
  · intro identity authority incoming reachable
    exact False.elim (unitNoReference reachable)
  · intro resident authority incoming reachable binding member
    simp [unitReachable reachable,unitValue,Value.resources] at member
  · intro source _ address support
    rcases support with ⟨resident,authority,access,reachable,observed⟩
    rcases observed with ⟨identity,loan,reference,found,referent⟩ | ⟨binding,member,addressEq⟩
    · simp [unitReachable reachable,unitValue,Value.head] at reference
    · simp [unitReachable reachable,unitValue,Value.resources] at member

private theorem permitted (access : Access) : Permitted world .owner access source := by
  refine ⟨⟨root,rfl⟩,?_⟩
  intro id loan found
  simp [world, Table.get] at found

private theorem resolved : ResolvesPlace world context.environment ⟨7,[]⟩ source (.shared .owner) := by
  refine .localSlot (binding := ⟨.localSlot 7,source,.shared .owner⟩) ⟨by simp [context],rfl,?_⟩ .nil
  intro other member _
  simpa [context] using member

private theorem sharedPermitted : Permitted world (.shared .owner) .shared source :=
  ⟨⟨root,rfl⟩,rfl,permitted .shared⟩

private theorem operands : ResolvedOperands world context.environment [⟨7,[]⟩] [⟨source,.shared .owner⟩] := by
  exact .cons ⟨resolved,sharedPermitted⟩ .nil

/-- A restricted view alone is not an invocation lease. The original
wrapper-only transition is now a rejected modeling regression. -/
example (program : RuntimeProgram) :
    ¬ BindsInput program 0 0 0 world ⟨.capture 0,.resident ⟨7,.unit,false⟩,source,.owner,.shared⟩
      ⟨.localSlot 7,source,.shared .owner⟩ world := by
  intro bound
  obtain ⟨_,impossible⟩ := bound.lent_authority (by decide) (by trivial)
  cases impossible

example (program : Kernel.Program) (binding : RuntimeBinding)
    (member : binding ∈ program.declarations.input.manifest.bindings)
    (safe : binding.signature.unsafeAllowed = false) :
    AtomStep program
      { world := world, task := .atom context destination (.primitive binding.declaration [] [⟨7,[]⟩]) .abort }
      none
      { world := world, task := .primitive context destination binding [] [⟨source,.shared .owner⟩] .abort } :=
  .primitive rfl member rfl operands (by simp [safe])

private theorem noSharedTransfer {program : RuntimeProgram} {world : World} {source destination : Address} {backing : Authority} {after : World} :
    ¬ Transfers program world (.shared backing) source destination after := by
  intro transfer
  cases shared_authority_cannot_strengthen transfer.permission

private theorem noSharedProtection {program : Kernel.Program} {context : Execution.Context}
    {world : World} {source destination : Address} {backing : Authority} {after : World} :
    ¬ Protect program context world source (.shared backing) destination after := by
  rintro ⟨_,_,_,_,transfer⟩
  exact noSharedTransfer transfer

private theorem noSharedExhausted {program : Kernel.Program} {context : Execution.Context}
    {world : World} {source : Address} {backing : Authority} :
    ¬ ProtectExhausted program context world source (.shared backing) := by
  rintro ⟨_,_,_,_,_,permission,_⟩
  cases shared_authority_cannot_strengthen permission

private theorem noSharedAttempt {program : Kernel.Program} {context : Execution.Context}
    {world : World} {source : Address} {backing : Authority} {rest : List ResolvedPlace}
    {footprint destinations : List Address} {after : World} {outcome : PreparationOutcome} :
    ¬ ProtectsAttemptFor program context footprint world
      (⟨source,.shared backing⟩ :: rest) destinations after outcome := by
  intro attempt
  cases attempt with
  | cons _ head _ => exact noSharedProtection head
  | exhausted _ exhausted => exact noSharedExhausted exhausted

private theorem noSharedHandoff {program : Kernel.Program} {context : Execution.Context} {world : World}
    {source : Address} {backing : Authority} {rest : List ResolvedPlace} {destinations : List Address} {after : World} :
    ¬ Protects program context world (⟨source,.shared backing⟩ :: rest) destinations after := by
  intro handoff
  cases handoff with
  | cons _ head _ =>
      rcases head with ⟨_,_,_,_,transfer⟩
      exact noSharedTransfer transfer

example (program : RuntimeProgram) (world after : World) (source destination : Address)
    (backing : Authority) (type : Term) (head : ValueHead) (rest : List ResolvedPlace) :
    ¬ NewValue program world destination type head (⟨source,.shared backing⟩ :: rest) after := by
  intro constructed
  cases shared_authority_cannot_strengthen (constructed.inputPermission (source := ⟨source,.shared backing⟩) (by simp))

example (program : RuntimeProgram) (world after : World) (source destination : Address)
    (backing : Authority) (pointer : RawPointer) (type : Term) :
    ¬ RawWrite program world ⟨source,backing.shared⟩ ⟨destination,backing⟩ pointer type after := by
  intro write
  cases write with
  | write _ _ _ _ _ _ transfer => exact noSharedTransfer transfer

/-- The same address is consumable through its actual owner. The old bug
was losing the input's view, not an absent global ownership restriction. -/
example : Permitted world .owner .owned source ∧ ¬ Permitted world (.shared .owner) .owned source := by
  refine ⟨permitted .owned,?_⟩
  intro permission
  cases shared_authority_cannot_strengthen permission

private def cleared : World := { world with roots := world.roots.set 0 { root with value := none } }
private def packed : World :=
  { cleared with roots := cleared.roots.set 1 { emptyRoot with
      value := some (.resident 1 (.tuple [.unit]) .tuple true [some unitValue]) }, nextOwner := 2 }

example (program : RuntimeProgram) :
    NewValue program world destination (.tuple [.unit]) .tuple [⟨source,.owner⟩] packed := by
  refine .construct (before := world) (destination := destination) (sources := [⟨source,.owner⟩])
    (taken := cleared) (residents := [unitValue])
    ⟨emptyRoot,rfl,Or.inl ⟨rfl,rfl⟩⟩ ⟨0,.root (root := emptyRoot) (id := 1) rfl rfl⟩
    ⟨.cons rfl .nil,?_,by simp,?_⟩ ?_ (.cons rfl .nil) rfl
  · intro resident member
    simp only [List.mem_singleton] at member
    subst resident
    exact ⟨initialized,unitReady program world _⟩
  · intro place member
    simp only [List.mem_singleton] at member
    subst place
    exact permitted .owned
  · intro place member
    simp only [List.mem_singleton] at member
    subst place
    simp [source,destination,Address.Overlaps]

/-- Distinct field paths are insufficient: moving both a container and its
child would duplicate an owner. Construction requires nonoverlap. -/
example (program : RuntimeProgram) (world after : World) (parent destination : Address)
    (index : Nat) (authority : Authority) (type : Term) (head : ValueHead) :
    ¬ NewValue program world destination type head
      [⟨parent,authority⟩,⟨parent.child index,authority⟩] after := by
  intro constructed
  cases constructed with
  | construct _ _ ready _ _ _ =>
      have apart := (List.pairwise_cons.mp ready.2.2.1).1 ⟨parent.child index,authority⟩ (by simp)
      exact apart ⟨rfl,rfl,Or.inr ⟨[index],rfl⟩⟩

example (program : Kernel.Program) (model : Foreign.Model) (state : State) (context : Execution.Context)
    (destination source : Address) (backing : Authority) (binding : RuntimeBinding) (arguments : List Term)
    (next : Code) (event : Option Event) (after : State) :
    ¬ Foreign.Step program model
      { state with task := .primitive context destination binding arguments [⟨source,.shared backing⟩] next }
      event after := by
  intro step
  cases step <;> simp_all
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := (by assumption :
    context = _ ∧ destination = _ ∧ binding = _ ∧ arguments = _ ∧
      ([⟨source,.shared backing⟩] : List ResolvedPlace) = _ ∧ next = _)
  exact noSharedHandoff (by assumption)

example (program : Kernel.Program) (state : State) (context : Execution.Context)
    (source : Address) (backing : Authority) (brand : Identity) (event : Option Event) (after : State) :
    ¬ ControlStep program
      { state with task := .leave context brand ⟨source,.shared backing⟩ }
      event after := by
  intro step
  cases step <;> simp_all
  all_goals obtain ⟨rfl,rfl,rfl⟩ := (by assumption :
    context = _ ∧ brand = _ ∧ (⟨source,.shared backing⟩ : ResolvedPlace) = _)
  all_goals first
    | exact noSharedExhausted (by assumption)
    | exact noSharedProtection (by assumption)

/-- Resource exhaustion can fault before inspecting the argument. Successful
replay, unlike that fault, must transfer the argument with owned permission. -/
example (program : Kernel.Program) (state : State) (context : Execution.Context)
    (source : Address) (backing : Authority) (id : Identity) (replay : Bool)
    (after : State) :
    ¬ EffectStep program
      { state with task := .resume context id ⟨source,.shared backing⟩ false }
      (some (.replay id replay)) after := by
  intro step
  cases step <;> simp_all
  all_goals obtain ⟨rfl,rfl⟩ := (by assumption :
    context = _ ∧ (⟨source,.shared backing⟩ : ResolvedPlace) = _)
  all_goals exact noSharedProtection (by assumption)

example (program : Kernel.Program) (state : State) (context : Execution.Context)
    (source : Address) (backing : Authority) (operation : DeclId) (arguments : List Term)
    (event : Option Event) (after : State) :
    ¬ EffectStep program
      { state with task := .perform context operation arguments [⟨source,.shared backing⟩] }
      event after := by
  intro step
  cases step <;> simp_all
  all_goals obtain ⟨rfl,rfl,rfl,rfl⟩ := (by assumption :
    context = _ ∧ operation = _ ∧ arguments = _ ∧
      ([⟨source,.shared backing⟩] : List ResolvedPlace) = _)
  all_goals first
    | exact noSharedHandoff (by assumption)
    | exact noSharedAttempt (by assumption)

private def scalar : ScalarValue := .integer false (.fixed 8) 7
private def scalarValue : Value := .resident 0 (.scalar scalar.type) (.scalar scalar) true []
private def scalarWorld : World :=
  { world with roots := world.roots.set 0 { root with type := .scalar scalar.type, value := some scalarValue } }

/-- Shared operands remain usable by reading primitives; preserving authority
does not restrict all primitive inputs to owners. -/
example : ScalarAt scalarWorld ⟨source,.shared .owner⟩ scalar := by
  refine ⟨⟨⟨_,rfl⟩,rfl,⟨⟨_,rfl⟩,?_⟩⟩,scalarValue,rfl,rfl,?_⟩
  · intro id loan found
    simp [scalarWorld, world, Table.get] at found
  · intro path resident location
    cases location with
    | root => simp [scalarValue, Value.shellLive, Value.fields]
    | field member _ => simp [scalarValue, Value.fields] at member

private def loan : Loan := ⟨0,none,source,.unique,0,true,.restoring,[],false,none⟩
private def loanWorld : World := { world with loans := [(0,loan)], nextLoan := 1 }
private def loanCleared : World := { cleared with loans := [(0,loan)], nextLoan := 1 }
private def loanPacked : World := { packed with loans := [(0,loan)], nextLoan := 1 }

private theorem loanPermission : Permitted loanWorld (.loan 0) .owned source := by
  refine ⟨⟨root,rfl⟩,loan,rfl,rfl,rfl,rfl,⟨[],rfl⟩,(fun _ => rfl),?_,?_,?_⟩
  · intro other resident found _ different
    simp [loanWorld, Table.get] at found
    exact False.elim (different found.1.symm)
  · simp [loan]
  · intro other resident found _ guarded
    simp [loanWorld,Table.get] at found
    rcases found with ⟨rfl,rfl⟩
    simp [loan] at guarded

/-- A unique-loan input is not an owner input: the loan blocks fabricated
owner access, while its retained authority admits the real field transfer. -/
example (program : RuntimeProgram) :
    ¬ Permitted loanWorld .owner .owned source ∧
    NewValue program loanWorld destination (.tuple [.unit]) .tuple [⟨source,.loan 0⟩] loanPacked := by
  constructor
  · intro permission
    have conflict := permission.2 0 loan rfl rfl ⟨rfl,rfl,Or.inl ⟨[],rfl⟩⟩
    exact conflict (Or.inr rfl)
  · refine .construct (before := loanWorld) (destination := destination) (sources := [⟨source,.loan 0⟩])
      (taken := loanCleared) (residents := [unitValue])
      ⟨emptyRoot,rfl,Or.inl ⟨rfl,rfl⟩⟩ ⟨0,.root (root := emptyRoot) (id := 1) rfl rfl⟩
      ⟨.cons rfl .nil,?_,by simp,?_⟩ ?_ (.cons rfl .nil) rfl
    · intro resident member
      simp only [List.mem_singleton] at member
      subst resident
      exact ⟨initialized,unitReady program loanWorld _⟩
    · intro place member
      simp only [List.mem_singleton] at member
      subst place
      exact loanPermission
    · intro place member
      simp only [List.mem_singleton] at member
      subst place
      simp [source,destination,Address.Overlaps]

end Glorious.Language.AuthorityChecks
